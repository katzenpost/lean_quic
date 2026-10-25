/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import LeanQUIC.Recovery

/-! # Recovery tests -/

open LeanQUIC.Recovery

namespace LeanQUIC.Tests.Recovery

def ms (n : Nat) : Nat := n * 1000

def pkt (pn t : Nat) (size := 1200) (ae := true) (inFlight := true) : SentPacket :=
  { pn, timeSent := t, ackEliciting := ae, inFlight, size }

def sendMany (s : State) (sp : Space) (pns : List Nat) (time : Nat → Nat) : State :=
  pns.foldl (fun s pn => onPacketSent s sp (pkt pn (time pn))) s

structure Ctx where
  fails : IO.Ref Nat

def check (c : Ctx) (name : String) (ok : Bool) (detail : String := "") : IO Unit := do
  if ok then IO.println s!"  ok   {name}"
  else
    IO.println s!"  FAIL {name} {detail}"
    c.fails.modify (· + 1)

def eq {α : Type} [BEq α] [Repr α] (c : Ctx) (name : String) (got want : α) : IO Unit :=
  check c name (got == want) s!"got {repr got}, want {repr want}"

/-- A server with the handshake confirmed (all PTO rules active for application data). -/
def server : State := setHandshakeConfirmed (init false)

def testRtt (c : Ctx) : IO Unit := do
  IO.println "RTT estimation (RFC 9002 §5)"
  let s := server
  eq c "initial smoothed_rtt 333 ms" (smoothedRtt s) 333000
  eq c "initial rttvar 166.5 ms" (rttVar s) 166500
  eq c "no min_rtt yet" (minRtt s) none
  -- first sample: 100 ms
  let s := onPacketSent s .application (pkt 0 0)
  let (s, r) := onAckReceived s .application [(0, 0)] (ms 10) (ms 100)
  eq c "acked [0]" r.acked [0]
  eq c "first sample smoothed = latest" (smoothedRtt s) 100000
  eq c "first sample rttvar = latest/2" (rttVar s) 50000
  eq c "first sample min_rtt" (minRtt s) (some 100000)
  -- 120 ms with 10 ms ack delay: adjusted 110 ms
  let s := onPacketSent s .application (pkt 1 (ms 200))
  let (s, _) := onAckReceived s .application [(1, 1)] (ms 10) (ms 320)
  eq c "rttvar = 3/4·50 + 1/4·|100-110| = 40 ms" (rttVar s) 40000
  eq c "smoothed = 7/8·100 + 1/8·110 = 101.25 ms" (smoothedRtt s) 101250
  -- 130 ms with 50 ms ack delay capped at max_ack_delay 25 ms: adjusted 105 ms
  let s := onPacketSent s .application (pkt 2 (ms 400))
  let (s, _) := onAckReceived s .application [(2, 2)] (ms 50) (ms 530)
  eq c "ack delay capped at max_ack_delay: rttvar" (rttVar s) 30937
  eq c "ack delay capped at max_ack_delay: smoothed" (smoothedRtt s) 101718
  eq c "min_rtt unchanged" (minRtt s) (some 100000)
  -- latest < min_rtt + ack_delay: no adjustment
  let s1 := onPacketSent s .application (pkt 3 (ms 600))
  let (s1, _) := onAckReceived s1 .application [(3, 3)] (ms 10) (ms 705)
  eq c "no adjustment below min_rtt + ack_delay" (smoothedRtt s1) ((7 * 101718 + 105000) / 8)
  -- larger max_ack_delay lets the full delay count
  let s2 := setMaxAckDelay s 100000
  let s2 := onPacketSent s2 .application (pkt 3 (ms 600))
  let (s2, _) := onAckReceived s2 .application [(3, 3)] (ms 50) (ms 760)
  eq c "max_ack_delay 100 ms: 160 - 50 = 110 ms" (smoothedRtt s2) ((7 * 101718 + 110000) / 8)
  -- ack delay ignored in the handshake space
  let h := init false
  let h := onPacketSent h .handshake (pkt 0 0)
  let (h, _) := onAckReceived h .handshake [(0, 0)] 0 (ms 100)
  let h := onPacketSent h .handshake (pkt 1 (ms 200))
  let (h, _) := onAckReceived h .handshake [(1, 1)] (ms 10) (ms 320)
  eq c "handshake space ignores ack delay" (smoothedRtt h) ((7 * 100000 + 120000) / 8)
  -- ack delay ignored before confirmation
  let u := init false
  let u := onPacketSent u .application (pkt 0 0)
  let (u, _) := onAckReceived u .application [(0, 0)] 0 (ms 100)
  let u := onPacketSent u .application (pkt 1 (ms 200))
  let (u, _) := onAckReceived u .application [(1, 1)] (ms 10) (ms 320)
  eq c "unconfirmed application ignores ack delay" (smoothedRtt u) ((7 * 100000 + 120000) / 8)
  -- RTT not sampled when the largest acked is not newly acked
  let n := onPacketSent server .application (pkt 0 0)
  let n := onPacketSent n .application (pkt 1 0)
  let (n, _) := onAckReceived n .application [(1, 1)] 0 (ms 50)
  let (n, _) := onAckReceived n .application [(0, 1)] 0 (ms 500)
  eq c "no sample when largest acked already acked" (smoothedRtt n) 50000
  -- RTT not sampled from non-ack-eliciting packets only
  let q := onPacketSent server .application (pkt 0 0 (ae := false) (inFlight := false))
  let (q, r) := onAckReceived q .application [(0, 0)] 0 (ms 50)
  eq c "non-ack-eliciting acked" r.acked [0]
  eq c "no sample from non-ack-eliciting" (minRtt q) none

def testLoss (c : Ctx) : IO Unit := do
  IO.println "Loss detection"
  let s := sendMany server .application [0, 1, 2, 3, 4] ms
  eq c "bytes in flight 5 packets" (bytesInFlight s) 6000
  let (s, r) := onAckReceived s .application [(4, 4)] 0 (ms 50)
  eq c "acked [4]" r.acked [4]
  eq c "packet threshold: 0 and 1 lost" r.lost [(.application, 0), (.application, 1)]
  eq c "latest rtt 46 ms" (smoothedRtt s) 46000
  -- loss_time for pn 2: 2 ms + 9/8·46 ms = 53.75 ms
  eq c "time threshold timer armed" (lossDetectionDeadline s) (some 53750)
  eq c "bytes in flight after loss" (bytesInFlight s) 2400
  let (s', t) := onLossDetectionTimeout s 53000
  eq c "early timeout is a no-op" t.lost []
  eq c "early timeout keeps deadline" (lossDetectionDeadline s') (some 53750)
  let (s, t) := onLossDetectionTimeout s 53750
  eq c "time threshold: 2 lost" t.lost [(.application, 2)]
  eq c "no probe on time-threshold loss" t.probe none
  eq c "next loss time for pn 3" (lossDetectionDeadline s) (some 54750)
  let (s, t) := onLossDetectionTimeout s 54750
  eq c "time threshold: 3 lost" t.lost [(.application, 3)]
  eq c "all packets resolved" (bytesInFlight s) 0
  eq c "nothing ack-eliciting in flight" (ackElicitingInFlight s .application) false
  eq c "idle server: no timer" (lossDetectionDeadline s) none
  -- ranges in any order, duplicates, and huge ranges over a small map
  let s := sendMany server .application [10, 11, 12, 13, 20] (fun _ => 0)
  let (s, r) := onAckReceived s .application [(20, 20), (0, 11)] 0 (ms 10)
  eq c "multi-range ack" r.acked [20, 10, 11]
  eq c "12, 13 lost by packet threshold" r.lost [(.application, 12), (.application, 13)]
  let (s, r) := onAckReceived s .application [(0, 1000000000)] 0 (ms 11)
  eq c "duplicate ack acks nothing" r.acked []
  eq c "everything resolved" (bytesInFlight s) 0

def testPto (c : Ctx) : IO Unit := do
  IO.println "PTO"
  let s := onPacketSent server .application (pkt 0 0)
  -- 333 + 4·166.5 + 25 ms
  eq c "ptoDuration application" (ptoDuration s .application) 1024000
  eq c "ptoDuration handshake" (ptoDuration s .handshake) 999000
  eq c "PTO armed" (lossDetectionDeadline s) (some 1024000)
  let (s, t) := onLossDetectionTimeout s 1024000
  eq c "PTO probe: 2 application packets" t.probe (some (.application, 2))
  eq c "PTO declares nothing lost" t.lost []
  eq c "backoff ×2 from last ack-eliciting send" (lossDetectionDeadline s) (some 2048000)
  let s := onPacketSent s .application (pkt 1 1024000)
  let s := onPacketSent s .application (pkt 2 1024000)
  eq c "probes rearm from probe send time" (lossDetectionDeadline s) (some (1024000 + 2048000))
  let (s, t) := onLossDetectionTimeout s 3072000
  eq c "second PTO" t.probe (some (.application, 2))
  eq c "backoff ×4" (lossDetectionDeadline s) (some (1024000 + 4096000))
  let (s, _) := onAckReceived s .application [(2, 2)] 0 3100000
  eq c "ack resets pto_count" (lossDetectionDeadline s).isSome true
  check c "pto_count reset" (s.ptoCount == 0)
  -- application data before handshake confirmation does not arm the PTO
  let u := onPacketSent (init false) .application (pkt 0 0)
  eq c "no app PTO before confirmation" (lossDetectionDeadline u) none
  let u := setHandshakeConfirmed u
  eq c "app PTO after confirmation" (lossDetectionDeadline u) (some 1024000)
  -- earliest space wins
  let m := onPacketSent (init false) .initial (pkt 0 (ms 10))
  let m := onPacketSent m .handshake (pkt 0 (ms 5))
  eq c "earliest of initial/handshake" (lossDetectionDeadline m) (some (ms 5 + 999000))
  let (_, t) := onLossDetectionTimeout m (ms 5 + 999000)
  eq c "probe in handshake space" t.probe (some (.handshake, 2))
  -- discarding a space
  let d := sendMany (init true) .initial [0, 1, 2] (fun _ => 0)
  eq c "client initial in flight" (bytesInFlight d) 3600
  let d := discardSpace d .initial
  eq c "discard drops bytes in flight" (bytesInFlight d) 0
  eq c "discarded space has nothing in flight" (ackElicitingInFlight d .initial) false
  let d := onPacketSent d .initial (pkt 3 0)
  eq c "sends in discarded space are ignored" (bytesInFlight d) 0
  let (_, r) := onAckReceived d .initial [(0, 3)] 0 (ms 1)
  eq c "acks in discarded space are ignored" r.acked []

def testAmplification (c : Ctx) : IO Unit := do
  IO.println "Server amplification limit"
  let s := onPacketSent (init false) .initial (pkt 0 0)
  eq c "timer armed" (lossDetectionDeadline s) (some 999000)
  let s := setAmplificationLimited s true
  eq c "amplification-limited server has no timer" (lossDetectionDeadline s) none
  let (_, t) := onLossDetectionTimeout s 5000000
  eq c "no probe while blocked" t.probe none
  let s := setAmplificationLimited s false
  eq c "timer re-armed when unblocked" (lossDetectionDeadline s) (some 999000)

def testAntiDeadlock (c : Ctx) : IO Unit := do
  IO.println "Client anti-deadlock PTO"
  let s := onPacketSent (init true) .initial (pkt 0 0)
  let (s, _) := onAckReceived s .initial [(0, 0)] 0 (ms 100)
  eq c "nothing in flight" (ackElicitingInFlight s .initial) false
  -- now + smoothed 100 + 4·50 ms
  eq c "anti-deadlock timer armed" (lossDetectionDeadline s) (some (ms 100 + ms 300))
  let (s1, t) := onLossDetectionTimeout s (ms 400)
  eq c "padded Initial probe" t.probe (some (.initial, 1))
  eq c "anti-deadlock backs off" (lossDetectionDeadline s1) (some (ms 400 + ms 600))
  let s2 := setHandshakeKeys s
  let (_, t) := onLossDetectionTimeout s2 (ms 400)
  eq c "Handshake probe once keys exist" t.probe (some (.handshake, 1))
  -- pto_count not reset by acks until address validation
  let s3 := onPacketSent s1 .initial (pkt 1 (ms 400))
  let (s3, _) := onAckReceived s3 .initial [(1, 1)] 0 (ms 500)
  check c "pto_count kept without address validation" (s3.ptoCount == 1)
  let s4 := setPeerCompletedAddressValidation s
  eq c "no timer once peer validated address" (lossDetectionDeadline s4) none
  let fresh := init true
  eq c "no timer before anything was sent" (lossDetectionDeadline fresh) none

def testPersistent (c : Ctx) : IO Unit := do
  IO.println "Persistent congestion"
  let base := onPacketSent server .application (pkt 0 0)
  let (base, _) := onAckReceived base .application [(0, 0)] 0 (ms 10)
  eq c "rtt 10 ms" (smoothedRtt base) 10000
  -- duration = (10 + 20 + 25)·3 = 165 ms
  let run (spacing : Nat) (ackedMid : Bool) : State × AckResult :=
    let s := sendMany base .application (List.range' 1 10) (fun pn => ms (10 + spacing * pn))
    let s := onPacketSent s .application (pkt 11 (ms 300) (ae := false) (inFlight := false))
    let rs := if ackedMid then [(11, 11), (5, 5)] else [(11, 11)]
    onAckReceived s .application rs 0 (ms 310)
  let (s, r) := run 20 false
  eq c "10 packets lost" r.lost.length 10
  eq c "cwnd collapses to kMinimumWindow" (congestionWindow s) (kMinimumWindow 1200)
  eq c "bytes in flight 0" (bytesInFlight s) 0
  let (s, _) := run 10 false
  eq c "short loss span: only halved" (congestionWindow s) 6600
  let (s, r) := run 20 true
  eq c "acked packet splits run" r.lost.length 9
  eq c "split run: only halved" (congestionWindow s) 6600
  -- packets sent before the first RTT sample don't count
  let p := sendMany server .application (List.range' 0 10) (fun pn => ms (20 * pn))
  let p := onPacketSent p .application (pkt 10 (ms 300) (ae := false) (inFlight := false))
  let p := onPacketSent p .application (pkt 11 (ms 300))
  let (p, r) := onAckReceived p .application [(11, 11)] 0 (ms 310)
  eq c "sampled on same ack" (minRtt p) (some (ms 10))
  eq c "lost before first sample: no persistent congestion"
    (r.lost.length, congestionWindow p) (10, 6000)

def testCongestion (c : Ctx) : IO Unit := do
  IO.println "Slow start, recovery, congestion avoidance"
  let s := server
  eq c "kInitialWindow 1200" (congestionWindow s) 12000
  eq c "kInitialWindow 1500" (congestionWindow (init true 1500)) 14720
  eq c "kInitialWindow 9000" (congestionWindow (init true 9000)) 18000
  eq c "send allowance" (sendAllowance s) 12000
  let s := sendMany s .application (List.range 10) (fun _ => 0)
  eq c "window full" (sendAllowance s) 0
  let (s, _) := onAckReceived s .application [(0, 9)] 0 (ms 100)
  eq c "slow start doubles" (congestionWindow s) 24000
  let s := sendMany s .application (List.range' 10 20) (fun pn => ms 200 + pn)
  let (s, r) := onAckReceived s .application [(13, 14)] 0 (ms 300)
  eq c "10, 11 lost" r.lost [(.application, 10), (.application, 11)]
  eq c "halved on loss" (congestionWindow s) 12000
  let (s, r) := onAckReceived s .application [(15, 29)] 0 (ms 301)
  eq c "12 lost" r.lost [(.application, 12)]
  eq c "single reduction per recovery period" (congestionWindow s) 12000
  eq c "all resolved" (bytesInFlight s) 0
  let s := sendMany s .application (List.range' 30 5) (fun _ => ms 400)
  let (s, _) := onAckReceived s .application [(30, 30)] 0 (ms 500)
  eq c "congestion avoidance: no growth before a full window" (congestionWindow s) 12000
  let (s, r) := onAckReceived s .application [(34, 34)] 0 (ms 501)
  eq c "31 lost" r.lost [(.application, 31)]
  eq c "new recovery period halves again" (congestionWindow s) 6000
  -- congestion avoidance: +1 MSS per cwnd of acked bytes
  let ca := sendMany s .application (List.range' 40 5) (fun _ => ms 600)
  let (ca, _) := onAckReceived ca .application [(40, 44)] 0 (ms 700)
  eq c "congestion avoidance +1 MSS per window" (congestionWindow ca) 7200
  -- the window never goes below the minimum
  let lowS := (List.range 6).foldl (fun s i =>
    let t := ms (1000 * (i + 1))
    let s := sendMany s .application (List.range' (100 + 10 * i) 4) (fun _ => t)
    (onAckReceived s .application [(100 + 10 * i + 3, 100 + 10 * i + 3)] 0 (t + ms 10)).1) server
  eq c "repeated losses floor at kMinimumWindow" (congestionWindow lowS) 2400

/-- 64-bit LCG. -/
def lcg (x : UInt64) : UInt64 := x * 6364136223846793005 + 1442695040888963407

structure Sim where
  s : State
  rng : UInt64 := 42
  now : Nat := 0
  nextPn : Nat := 0
  dataSent : Nat := 0
  /-- 0 = outstanding, 1 = acked, 2 = lost, 3 = reported twice. -/
  status : Array Nat := #[]
  dropped : Array Bool := #[]
  /-- In transit to the receiver: (arrival, pn). -/
  toPeer : Array (Nat × Nat) := #[]
  toPeerHead : Nat := 0
  /-- In transit to the sender: (arrival, ranges). -/
  toUs : Array (Nat × List (Nat × Nat)) := #[]
  toUsHead : Nat := 0
  recent : List Nat := []
  outstanding : Nat := 0
  bifMismatch : Nat := 0
  timeouts : Nat := 0
  probes : Nat := 0
  lossPct : UInt64 := 5

def oneWay : Nat := ms 20

def Sim.send (m : Sim) : Sim :=
  let pn := m.nextPn
  let rng := lcg m.rng
  let drop := (rng >>> 33) % 100 < m.lossPct
  let s := onPacketSent m.s .application (pkt pn m.now)
  { m with s, rng, nextPn := pn + 1, status := m.status.push 0, dropped := m.dropped.push drop,
           toPeer := if drop then m.toPeer else m.toPeer.push (m.now + oneWay, pn),
           outstanding := m.outstanding + 1200 }

def Sim.mark (m : Sim) (pn v : Nat) : Sim :=
  let cur := m.status[pn]!
  let outstanding := if cur == 0 then m.outstanding - 1200 else m.outstanding
  { m with status := m.status.set! pn (if cur == 0 then v else 3), outstanding }

def Sim.step (m : Sim) (total : Nat) : Sim := Id.run do
  let mut m := m
  -- receiver: ack each arriving packet with the three most recent pns
  while h : m.toPeerHead < m.toPeer.size do
    let (t, pn) := m.toPeer[m.toPeerHead]
    if m.now < t then break
    let recent := (pn :: m.recent).take 3
    m := { m with toPeerHead := m.toPeerHead + 1, recent,
                  toUs := m.toUs.push (t + oneWay, recent.map fun p => (p, p)) }
  while h : m.toUsHead < m.toUs.size do
    let (t, ranges) := m.toUs[m.toUsHead]
    if m.now < t then break
    let (s, r) := onAckReceived m.s .application ranges 0 m.now
    m := { m with s, toUsHead := m.toUsHead + 1 }
    for pn in r.acked do m := m.mark pn 1
    for (_, pn) in r.lost do m := m.mark pn 2
  if let some d := lossDetectionDeadline m.s then
    if d ≤ m.now then
      let (s, r) := onLossDetectionTimeout m.s m.now
      m := { m with s, timeouts := m.timeouts + 1 }
      for (_, pn) in r.lost do m := m.mark pn 2
      if let some (_, k) := r.probe then
        for _ in [0:k] do m := { m.send with probes := m.probes + 1 }
  while m.dataSent < total && 1200 ≤ sendAllowance m.s do
    m := { m.send with dataSent := m.dataSent + 1 }
  if bytesInFlight m.s != m.outstanding then m := { m with bifMismatch := m.bifMismatch + 1 }
  return m

def simulate (total : Nat) (lossPct : UInt64 := 5) : Sim := Id.run do
  let mut m : Sim := { s := server, lossPct }
  for _ in [0:1000000] do
    m := m.step total
    if m.dataSent == total && m.outstanding == 0 && m.toUsHead == m.toUs.size then break
    m := { m with now := m.now + 1000 }
  return m

def runSim (c : Ctx) (total : Nat) (lossPct : UInt64) : IO Unit := do
  IO.println s!"Simulated transfer: {total} packets, {lossPct}% loss"
  let t0 ← IO.monoNanosNow
  let m ← IO.lazyPure fun _ => simulate total lossPct
  let t1 ← IO.monoNanosNow
  let n := m.nextPn
  let acked := (m.status.filter (· == 1)).size
  let lost := (m.status.filter (· == 2)).size
  let dropped := (m.dropped.filter id).size
  IO.println s!"  sent {n} (probes {m.probes}), acked {acked}, lost {lost}, dropped {dropped}, \
    timeouts {m.timeouts}, simulated {m.now / 1000} ms, final cwnd {congestionWindow m.s}"
  eq c "all data sent" m.dataSent total
  eq c "every packet acked or lost exactly once" (acked + lost) n
  check c "no double reports" (!m.status.contains 3)
  check c "no outstanding packets" (!m.status.contains 0)
  check c "every dropped packet declared lost"
    ((List.range n).all fun i => !m.dropped[i]! || m.status[i]! == 2)
  eq c "bytes_in_flight matched outstanding bytes at every step" m.bifMismatch 0
  eq c "bytes_in_flight returns to 0" (bytesInFlight m.s) 0
  let elapsed := (t1 - t0) / 1000000
  IO.println s!"  elapsed {elapsed} ms"
  check c "simulation under 1 s" (elapsed < 1000)

/-- 3000 packets in flight at once, acked one ACK frame per packet, every 20th dropped. -/
def bulk (n : Nat) : State × Nat × Nat := Id.run do
  let mut s := sendMany server .application (List.range n) (fun _ => 0)
  let mut acked := 0
  let mut lost := 0
  for pn in [0:n] do
    if pn % 20 == 0 then continue
    let (s', r) := onAckReceived s .application [(pn, pn), (pn / 20 * 20 + 1, pn)] 0 (ms 50 + pn)
    s := s'
    acked := acked + r.acked.length
    lost := lost + r.lost.length
  let (s', r) := onLossDetectionTimeout s (ms 1000)
  return (s', acked, lost + r.lost.length)

def testBulk (c : Ctx) : IO Unit := do
  IO.println "3000 packets in flight"
  let t0 ← IO.monoNanosNow
  let (s, acked, lost) ← IO.lazyPure fun _ => bulk 3000
  let t1 ← IO.monoNanosNow
  eq c "acked + lost = 3000" (acked, lost) (2850, 150)
  eq c "bytes_in_flight 0" (bytesInFlight s) 0
  let elapsed := (t1 - t0) / 1000000
  IO.println s!"  elapsed {elapsed} ms"
  check c "bulk under 1 s" (elapsed < 1000)

def testSimulation (c : Ctx) : IO Unit := do
  testBulk c
  runSim c 3000 5
  runSim c 3000 30
  runSim c 30000 5

end LeanQUIC.Tests.Recovery

open LeanQUIC.Tests.Recovery in
def main : IO UInt32 := do
  let c : Ctx := { fails := ← IO.mkRef 0 }
  testRtt c
  testLoss c
  testPto c
  testAmplification c
  testAntiDeadlock c
  testPersistent c
  testCongestion c
  testSimulation c
  let f ← c.fails.get
  if f == 0 then IO.println "all recovery tests passed"; return 0
  else IO.println s!"{f} recovery test(s) failed"; return 1
