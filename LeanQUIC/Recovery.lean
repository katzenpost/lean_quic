/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Std.Data.TreeMap

/-! # QUIC loss recovery

RFC 9002 loss detection (Appendix A) and NewReno congestion control (Appendix B).
Sans-IO: times are microseconds supplied by the caller, and send times within a
packet number space are assumed nondecreasing. -/

namespace LeanQUIC.Recovery

inductive Space where | initial | handshake | application
deriving DecidableEq, Repr, Inhabited

structure SentPacket where
  pn : Nat
  timeSent : Nat
  ackEliciting : Bool
  inFlight : Bool
  size : Nat
deriving Repr, Inhabited

structure AckResult where
  acked : List Nat
  lost  : List (Space × Nat)
deriving Repr, Inhabited

structure TimeoutResult where
  lost   : List (Space × Nat)
  /-- When nonempty: send this many (1 or 2) ack-eliciting probe packets in this space. -/
  probe  : Option (Space × Nat)
deriving Repr, Inhabited

def kPacketThreshold : Nat := 3
/-- Timer granularity, 1 ms. -/
def kGranularity : Nat := 1000
def kInitialRtt : Nat := 333000
def kPersistentCongestionThreshold : Nat := 3
def kDefaultMaxAckDelay : Nat := 25000

def kInitialWindow (mds : Nat) : Nat := min (10 * mds) (max 14720 (2 * mds))
def kMinimumWindow (mds : Nat) : Nat := 2 * mds

theorem kMinimumWindow_le_kInitialWindow (mds : Nat) :
    kMinimumWindow mds ≤ kInitialWindow mds := by
  simp only [kMinimumWindow, kInitialWindow]; omega

/-- Time-threshold loss delay: 9/8 × `rtt`, at least `kGranularity`. -/
def lossDelayOf (rtt : Nat) : Nat := max (rtt * 9 / 8) kGranularity

/-- Per packet number space recovery state. -/
structure SpaceState where
  sent : Std.TreeMap Nat SentPacket := {}
  largestAcked : Option Nat := none
  lossTime : Option Nat := none
  lastAckElicitingTime : Option Nat := none
  /-- Number of in-flight ack-eliciting packets in `sent`. -/
  ackElicitingCount : Nat := 0
  discarded : Bool := false

structure State where
  isClient : Bool
  maxDatagramSize : Nat
  maxAckDelay : Nat := kDefaultMaxAckDelay
  handshakeConfirmed : Bool := false
  peerValidated : Bool
  amplificationLimited : Bool := false
  hasHandshakeKeys : Bool := false
  latestRtt : Nat := 0
  smoothed : Nat := kInitialRtt
  rttvar : Nat := kInitialRtt / 2
  rttMin : Option Nat := none
  firstRttSampleTime : Option Nat := none
  ptoCount : Nat := 0
  /-- `now` at the last timer (re)arm; base of the anti-deadlock PTO. -/
  timerBase : Option Nat := none
  initialSpace : SpaceState := {}
  handshakeSpace : SpaceState := {}
  appSpace : SpaceState := {}
  cwnd : Nat
  cwnd_ge : kMinimumWindow maxDatagramSize ≤ cwnd
  inFlightBytes : Nat := 0
  /-- `none` is infinite. -/
  ssthresh : Option Nat := none
  recoveryStart : Option Nat := none
  /-- Bytes acked in congestion avoidance since the last window increase. -/
  caAcked : Nat := 0

def allSpaces : List Space := [.initial, .handshake, .application]

def State.space (s : State) : Space → SpaceState
  | .initial => s.initialSpace
  | .handshake => s.handshakeSpace
  | .application => s.appSpace

def State.setSpace (s : State) : Space → SpaceState → State
  | .initial, st => { s with initialSpace := st }
  | .handshake, st => { s with handshakeSpace := st }
  | .application, st => { s with appSpace := st }

def init (isClient : Bool) (maxDatagramSize : Nat := 1200) : State :=
  { isClient, maxDatagramSize, peerValidated := !isClient,
    cwnd := kInitialWindow maxDatagramSize,
    cwnd_ge := kMinimumWindow_le_kInitialWindow maxDatagramSize }

/-- Peer's max_ack_delay transport parameter, in µs (default 25 ms). -/
def setMaxAckDelay (s : State) (us : Nat) : State := { s with maxAckDelay := us }
def setHandshakeConfirmed (s : State) : State :=
  { s with handshakeConfirmed := true, peerValidated := true }
/-- Client: peer completed address validation (handshake ack received / handshake confirmed). Server: always true. -/
def setPeerCompletedAddressValidation (s : State) : State := { s with peerValidated := true }
/-- Server only: true while the anti-amplification limit blocks sending. -/
def setAmplificationLimited (s : State) (b : Bool) : State := { s with amplificationLimited := b }
/-- Handshake keys are available (also inferred from Handshake sends and Initial discard). -/
def setHandshakeKeys (s : State) : State := { s with hasHandshakeKeys := true }

def congestionWindow (s : State) : Nat := s.cwnd
def bytesInFlight (s : State) : Nat := s.inFlightBytes
/-- Bytes the congestion controller allows sending now: cwnd - bytes_in_flight (saturating). -/
def sendAllowance (s : State) : Nat := s.cwnd - s.inFlightBytes
def smoothedRtt (s : State) : Nat := s.smoothed
def rttVar (s : State) : Nat := s.rttvar
def minRtt (s : State) : Option Nat := s.rttMin

/-- `smoothed_rtt + max(4 × rttvar, kGranularity)`. -/
def baseDuration (s : State) : Nat := s.smoothed + max (4 * s.rttvar) kGranularity

/-- Current PTO duration for a space (without backoff, plus max_ack_delay for application space). -/
def ptoDuration (s : State) (space : Space) : Nat :=
  baseDuration s + (if space = .application then s.maxAckDelay else 0)

/-- Has any ack-eliciting packet in flight in the space. -/
def ackElicitingInFlight (s : State) (space : Space) : Bool :=
  (s.space space).ackElicitingCount != 0

def anyAckElicitingInFlight (s : State) : Bool :=
  ackElicitingInFlight s .initial || ackElicitingInFlight s .handshake ||
    ackElicitingInFlight s .application

private def minBy (a b : Option (Nat × Space)) : Option (Nat × Space) :=
  match a, b with
  | some x, some y => if y.1 < x.1 then some y else some x
  | some x, none => some x
  | none, y => y

/-- Earliest `loss_time` over all spaces (`GetLossTimeAndSpace`). -/
def earliestLossTime (s : State) : Option (Nat × Space) :=
  let f sp := (s.space sp).lossTime.map (·, sp)
  minBy (minBy (f .initial) (f .handshake)) (f .application)

/-- `GetPtoTimeAndSpace`; `none` is an infinite timeout. -/
def ptoTimeAndSpace (s : State) (now : Nat) : Option (Nat × Space) :=
  let backoff := 2 ^ s.ptoCount
  let dur := baseDuration s * backoff
  if !anyAckElicitingInFlight s then
    some (now + dur, if s.hasHandshakeKeys then .handshake else .initial)
  else
    let cand (sp : Space) (extra : Nat) : Option (Nat × Space) :=
      if ackElicitingInFlight s sp then
        (s.space sp).lastAckElicitingTime.map (· + dur + extra, sp)
      else none
    let app := if s.handshakeConfirmed then cand .application (s.maxAckDelay * backoff) else none
    minBy (minBy (cand .initial 0) (cand .handshake 0)) app

/-- Absolute deadline (µs) of the loss detection timer, if armed. -/
def lossDetectionDeadline (s : State) : Option Nat :=
  match earliestLossTime s with
  | some (t, _) => some t
  | none =>
    if s.amplificationLimited then none
    else if !anyAckElicitingInFlight s && s.peerValidated then none
    else match s.timerBase with
      | none => none
      | some base => (ptoTimeAndSpace s base).map (·.1)

/-- Sent times at or before the recovery start are in the recovery period. -/
def inRecovery (s : State) (sentTime : Nat) : Bool :=
  match s.recoveryStart with
  | some r => sentTime ≤ r
  | none => false

/-- `OnCongestionEvent`: halve the window once per recovery period. -/
def onCongestionEvent (s : State) (sentTime now : Nat) : State :=
  if inRecovery s sentTime then s
  else
    let half := s.cwnd / 2
    { s with recoveryStart := some now, ssthresh := some half, caAcked := 0,
             cwnd := max half (kMinimumWindow s.maxDatagramSize),
             cwnd_ge := Nat.le_max_right _ _ }

/-- Persistent congestion response: collapse to the minimum window. -/
def collapse (s : State) : State :=
  { s with cwnd := kMinimumWindow s.maxDatagramSize, cwnd_ge := Nat.le_refl _,
           recoveryStart := none, caAcked := 0 }

/-- RFC 9002 §7.6: two ack-eliciting packets sent after the first RTT sample, more than the
persistent congestion duration apart, with every packet between them lost. Each space's lost
packets come in ascending pn order; a pn gap ends a run. -/
def persistentCongestion (s : State) (lost : Array (Space × SentPacket)) : Bool :=
  match s.firstRttSampleTime with
  | none => false
  | some first =>
    let dur := (baseDuration s + s.maxAckDelay) * kPersistentCongestionThreshold
    allSpaces.any fun sp => Id.run do
      let mut prev : Option Nat := none
      let mut start : Option Nat := none
      for (sp', p) in lost do
        if sp' != sp then continue
        if prev.map (· + 1) != some p.pn then start := none
        prev := some p.pn
        if p.ackEliciting && first < p.timeSent then
          match start with
          | none => start := some p.timeSent
          | some t0 => if p.timeSent - t0 > dur then return true
      return false

/-- `OnPacketsLost`: bytes in flight, congestion event, persistent congestion. -/
def onPacketsLost (s : State) (lost : Array (Space × SentPacket)) (now : Nat) : State :=
  let bytes := lost.foldl (fun b (_, p) => if p.inFlight then b + p.size else b) 0
  let lastLoss := lost.foldl (init := none) fun acc (_, p) =>
    if p.inFlight then some (max (acc.getD 0) p.timeSent) else acc
  let s := { s with inFlightBytes := s.inFlightBytes - bytes }
  let s := match lastLoss with
    | some t => onCongestionEvent s t now
    | none => s
  if persistentCongestion s lost then collapse s else s

/-- `OnPacketAcked` (congestion control part). -/
def onPacketAckedCC (s : State) (p : SentPacket) : State :=
  if !p.inFlight then s
  else
    let s := { s with inFlightBytes := s.inFlightBytes - p.size }
    if inRecovery s p.timeSent then s
    else
      let slowStart := match s.ssthresh with
        | none => true
        | some t => s.cwnd < t
      if slowStart then
        { s with cwnd := s.cwnd + p.size, cwnd_ge := Nat.le_trans s.cwnd_ge (Nat.le_add_right _ _) }
      else
        let acc := s.caAcked + p.size
        if s.cwnd ≤ acc then
          { s with cwnd := s.cwnd + s.maxDatagramSize, caAcked := acc - s.cwnd,
                   cwnd_ge := Nat.le_trans s.cwnd_ge (Nat.le_add_right _ _) }
        else { s with caAcked := acc }

/-- `UpdateRtt` with a new `latest_rtt` sample. Ack delay counts only for application data
after handshake confirmation, capped at max_ack_delay. -/
def updateRtt (s : State) (space : Space) (latest ackDelay now : Nat) : State :=
  let s := { s with latestRtt := latest }
  match s.rttMin with
  | none =>
    { s with rttMin := some latest, smoothed := latest, rttvar := latest / 2,
             firstRttSampleTime := some now }
  | some m =>
    let m := min m latest
    let ad := if space = .application && s.handshakeConfirmed then min ackDelay s.maxAckDelay else 0
    let adj := if m + ad ≤ latest then latest - ad else latest
    let diff := if adj ≤ s.smoothed then s.smoothed - adj else adj - s.smoothed
    { s with rttMin := some m, rttvar := (3 * s.rttvar + diff) / 4,
             smoothed := (7 * s.smoothed + adj) / 8 }

private def countAE (n : Nat) (ps : Array SentPacket) : Nat :=
  ps.foldl (fun n p => if p.ackEliciting && p.inFlight then n - 1 else n) n

/-- `DetectAndRemoveLostPackets`. Only unacknowledged packets at or below the largest acked
are visited, since acked packets have already been removed. -/
def detectLost (s : State) (space : Space) (now : Nat) : SpaceState × Array SentPacket :=
  let st := s.space space
  match st.largestAcked with
  | none => ({ st with lossTime := none }, #[])
  | some la => Id.run do
    let delay := lossDelayOf (max s.latestRtt s.smoothed)
    let mut lost : Array SentPacket := #[]
    let mut lt : Option Nat := none
    for (pn, p) in st.sent do
      if la < pn then break
      if p.timeSent + delay ≤ now || pn + kPacketThreshold ≤ la then
        lost := lost.push p
      else
        let t := p.timeSent + delay
        lt := some (match lt with | none => t | some u => min u t)
    let sent := lost.foldl (fun m p => m.erase p.pn) st.sent
    return ({ st with sent, lossTime := lt, ackElicitingCount := countAE st.ackElicitingCount lost },
      lost)

/-- Removes the packets with pn in `[lo, hi]`, in O((k + 1) log n) for k removed packets. -/
def takeRange (sent : Std.TreeMap Nat SentPacket) (lo hi : Nat) (acc : Array SentPacket) :
    Std.TreeMap Nat SentPacket × Array SentPacket :=
  go sent.size sent lo acc
where
  go : Nat → Std.TreeMap Nat SentPacket → Nat → Array SentPacket →
      Std.TreeMap Nat SentPacket × Array SentPacket
    | 0, m, _, acc => (m, acc)
    | fuel + 1, m, k, acc =>
      match m.getEntryGE? k with
      | some (pn, p) => if pn ≤ hi then go fuel (m.erase pn) (pn + 1) (acc.push p) else (m, acc)
      | none => (m, acc)

private def toPairs (space : Space) (ps : Array SentPacket) : Array (Space × SentPacket) :=
  ps.map (space, ·)

private def pnList (ps : Array (Space × SentPacket)) : List (Space × Nat) :=
  ps.toList.map fun (sp, p) => (sp, p.pn)

def onPacketSent (s : State) (space : Space) (p : SentPacket) : State :=
  let st := s.space space
  if st.discarded || st.sent.contains p.pn then s
  else
    let st := { st with sent := st.sent.insert p.pn p }
    let st := if p.inFlight && p.ackEliciting then
        { st with lastAckElicitingTime := some p.timeSent, ackElicitingCount := st.ackElicitingCount + 1 }
      else st
    let s := s.setSpace space st
    let s := if space = .handshake then { s with hasHandshakeKeys := true } else s
    if p.inFlight then
      { s with inFlightBytes := s.inFlightBytes + p.size, timerBase := some p.timeSent }
    else s

/-- `ranges`: the ACK frame's acknowledged ranges as inclusive (smallest, largest), in any order. `ackDelay` already decoded to µs. -/
def onAckReceived (s : State) (space : Space) (ranges : List (Nat × Nat)) (ackDelay : Nat)
    (now : Nat) : State × AckResult :=
  let st := s.space space
  if st.discarded || ranges.isEmpty then (s, ⟨[], []⟩)
  else
    let ackLargest := ranges.foldl (fun m (a, b) => max m (max a b)) 0
    let la := match st.largestAcked with
      | none => ackLargest
      | some l => max l ackLargest
    let (sent, acked) := ranges.foldl (init := (st.sent, #[]))
      fun (m, acc) (a, b) => takeRange m (min a b) (max a b) acc
    let st := { st with largestAcked := some la, sent,
                        ackElicitingCount := countAE st.ackElicitingCount acked }
    let s := { s.setSpace space st with timerBase := some now }
    if acked.isEmpty then (s, ⟨[], []⟩)
    else
      let largestNew := acked.foldl (fun (q : SentPacket) p => if q.pn < p.pn then p else q) acked[0]!
      let s := if largestNew.pn = ackLargest && acked.any (·.ackEliciting) then
          updateRtt s space (now - largestNew.timeSent) ackDelay now
        else s
      let (st, lost) := detectLost s space now
      let s := s.setSpace space st
      let lost := toPairs space lost
      let s := if lost.isEmpty then s else onPacketsLost s lost now
      let s := acked.foldl onPacketAckedCC s
      let s := if s.peerValidated then { s with ptoCount := 0 } else s
      (s, ⟨acked.toList.map (·.pn), pnList lost⟩)

/-- `OnLossDetectionTimeout`. A call before the deadline (or with no timer armed) is a no-op. -/
def onLossDetectionTimeout (s : State) (now : Nat) : State × TimeoutResult :=
  match lossDetectionDeadline s with
  | none => (s, ⟨[], none⟩)
  | some d =>
    if now < d then (s, ⟨[], none⟩)
    else
      let s := { s with timerBase := some now }
      match earliestLossTime s with
      | some (_, sp) =>
        let (st, lost) := detectLost s sp now
        let lost := toPairs sp lost
        (onPacketsLost (s.setSpace sp st) lost now, ⟨pnList lost, none⟩)
      | none =>
        let probe : Space × Nat :=
          if !anyAckElicitingInFlight s then
            (if s.hasHandshakeKeys then .handshake else .initial, 1)
          else match ptoTimeAndSpace s now with
            | some (_, sp) => (sp, 2)
            | none => (.application, 2)
        ({ s with ptoCount := s.ptoCount + 1 }, ⟨[], some probe⟩)

/-- `OnPacketNumberSpaceDiscarded`: drop the space's packets from bytes in flight and reset PTO. -/
def discardSpace (s : State) (space : Space) : State :=
  let bytes := (s.space space).sent.foldl (fun b _ p => if p.inFlight then b + p.size else b) 0
  let s := s.setSpace space { discarded := true }
  let s := { s with inFlightBytes := s.inFlightBytes - bytes, ptoCount := 0 }
  if space = .initial then { s with hasHandshakeKeys := true } else s

/-! ## Laws -/

theorem sendAllowance_le_congestionWindow (s : State) : sendAllowance s ≤ congestionWindow s :=
  Nat.sub_le _ _

theorem congestionWindow_ge_minimum (s : State) :
    kMinimumWindow s.maxDatagramSize ≤ congestionWindow s :=
  s.cwnd_ge

theorem init_congestionWindow (c : Bool) (mds : Nat) :
    congestionWindow (init c mds) = kInitialWindow mds := rfl

theorem onCongestionEvent_maxDatagramSize (s : State) (t now : Nat) :
    (onCongestionEvent s t now).maxDatagramSize = s.maxDatagramSize := by
  unfold onCongestionEvent; split <;> rfl

/-- A loss event never grows the window and never takes it below the minimum. -/
theorem onCongestionEvent_cwnd (s : State) (t now : Nat) :
    kMinimumWindow s.maxDatagramSize ≤ congestionWindow (onCongestionEvent s t now) ∧
    congestionWindow (onCongestionEvent s t now) ≤ congestionWindow s := by
  have h := s.cwnd_ge
  unfold onCongestionEvent congestionWindow
  split
  · exact ⟨h, Nat.le_refl _⟩
  · simp only; omega

/-- Outside a recovery period a loss event halves the window (floored at the minimum). -/
theorem onCongestionEvent_halves (s : State) (t now : Nat) (h : inRecovery s t = false) :
    congestionWindow (onCongestionEvent s t now) =
      max (congestionWindow s / 2) (kMinimumWindow s.maxDatagramSize) := by
  simp [onCongestionEvent, congestionWindow, h]

/-- Inside a recovery period a further loss does not reduce the window again. -/
theorem onCongestionEvent_inRecovery (s : State) (t now : Nat) (h : inRecovery s t = true) :
    onCongestionEvent s t now = s := by
  simp [onCongestionEvent, h]

theorem collapse_cwnd (s : State) :
    congestionWindow (collapse s) = kMinimumWindow s.maxDatagramSize := rfl

/-- An amplification-limited server has no PTO timer. -/
theorem lossDetectionDeadline_amplificationLimited (s : State)
    (ha : s.amplificationLimited = true) (hl : earliestLossTime s = none) :
    lossDetectionDeadline s = none := by
  simp [lossDetectionDeadline, ha, hl]

/-- Nothing ack-eliciting in flight and the peer validated our address: no timer. -/
theorem lossDetectionDeadline_idle (s : State) (hv : s.peerValidated = true)
    (hi : anyAckElicitingInFlight s = false) (hl : earliestLossTime s = none) :
    lossDetectionDeadline s = none := by
  simp [lossDetectionDeadline, hv, hi, hl]

/-- Before handshake confirmation, application data alone never arms the PTO. -/
theorem ptoTimeAndSpace_app_unconfirmed (s : State) (now : Nat)
    (hc : s.handshakeConfirmed = false)
    (hi : ackElicitingInFlight s .initial = false) (hh : ackElicitingInFlight s .handshake = false)
    (ha : ackElicitingInFlight s .application = true) :
    ptoTimeAndSpace s now = none := by
  simp [ptoTimeAndSpace, anyAckElicitingInFlight, hc, hi, hh, ha, minBy]


/-! Dot-notation names for the operations on `State`. -/

@[inline] abbrev State.setMaxAckDelay := @LeanQUIC.Recovery.setMaxAckDelay
@[inline] abbrev State.setHandshakeConfirmed := @LeanQUIC.Recovery.setHandshakeConfirmed
@[inline] abbrev State.setPeerCompletedAddressValidation := @LeanQUIC.Recovery.setPeerCompletedAddressValidation
@[inline] abbrev State.setAmplificationLimited := @LeanQUIC.Recovery.setAmplificationLimited
@[inline] abbrev State.setHandshakeKeys := @LeanQUIC.Recovery.setHandshakeKeys
@[inline] abbrev State.congestionWindow := @LeanQUIC.Recovery.congestionWindow
@[inline] abbrev State.bytesInFlight := @LeanQUIC.Recovery.bytesInFlight
@[inline] abbrev State.sendAllowance := @LeanQUIC.Recovery.sendAllowance
@[inline] abbrev State.smoothedRtt := @LeanQUIC.Recovery.smoothedRtt
@[inline] abbrev State.rttVar := @LeanQUIC.Recovery.rttVar
@[inline] abbrev State.minRtt := @LeanQUIC.Recovery.minRtt
@[inline] abbrev State.ptoDuration := @LeanQUIC.Recovery.ptoDuration
@[inline] abbrev State.ackElicitingInFlight := @LeanQUIC.Recovery.ackElicitingInFlight
@[inline] abbrev State.lossDetectionDeadline := @LeanQUIC.Recovery.lossDetectionDeadline
@[inline] abbrev State.onPacketSent := @LeanQUIC.Recovery.onPacketSent
@[inline] abbrev State.onAckReceived := @LeanQUIC.Recovery.onAckReceived
@[inline] abbrev State.onLossDetectionTimeout := @LeanQUIC.Recovery.onLossDetectionTimeout
@[inline] abbrev State.discardSpace := @LeanQUIC.Recovery.discardSpace

end LeanQUIC.Recovery
