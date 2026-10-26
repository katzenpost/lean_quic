/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Std.Data.HashMap
import LeanQUIC.Sealer
import LeanQUIC.Frame
import LeanQUIC.TransportParams
import LeanQUIC.Recovery
import LeanQUIC.Buffers
import LeanQUIC.Error
import LeanTLS.Handshake.Client
import LeanTLS.Handshake.Server

namespace LeanQUIC

open LeanTLS.Handshake (Level Output Secrets)
open LeanTLS.Handshake.Client renaming Config → ClientConfig
open LeanTLS (Suite)
open Recovery (Space)

/-! # A QUIC connection, without IO

The connection is a value. `recv` gives it a datagram, `poll` asks it for the next datagram to
send, `onTimeout` tells it a deadline from `nextTimeout` has passed; the time is always an
argument, in microseconds. The application side opens, writes, reads and finishes bidirectional
streams. TLS runs in lean_tls's handshake state machines, fed from the CRYPTO streams.

Application data moves only once the handshake is complete: stream frames in 1-RTT packets are
accepted only after TLS has produced its `Established` evidence. -/

def Recovery.Space.ofLevel : Level → Space
  | .initial => .initial
  | .handshake => .handshake
  | .application => .application

def Recovery.Space.level : Space → Level
  | .initial => .initial
  | .handshake => .handshake
  | .application => .application

def maxDatagram : Nat := 1200
def cidLength : Nat := 8
/-- The CRYPTO reassembly cap per level. -/
def cryptoCap : Nat := 65536

inductive Tls where
  | client (cfg : LeanTLS.Handshake.Client.Config) (st : LeanTLS.Handshake.Client.State cfg)
  | server (cfg : LeanTLS.Handshake.Server.Config) (seed : Vector UInt8 32)
      (st : LeanTLS.Handshake.Server.State)

namespace Tls

def recv (t : Tls) (level : Level) (data : ByteArray) : Except LeanTLS.Alert (Tls × Array Output) :=
  match t with
  | .client cfg st => do
    let (st', out) ← LeanTLS.Handshake.Client.recv st level data
    pure (.client cfg st', out)
  | .server cfg seed st => do
    let (st', out) ← LeanTLS.Handshake.Server.recv cfg seed st level data
    pure (.server cfg seed st', out)

/-- The peer's transport parameters, once TLS has authenticated the handshake. -/
def established? : Tls → Option ByteArray
  | .client _ st => st.established?.map (·.peerTransportParams)
  | .server _ _ st => st.established?.map (·.peerTransportParams)

end Tls

/-- What a sent packet carried that must be resent if it is lost. -/
inductive Sent where
  | crypto (level : Level) (offset len : Nat)
  | stream (id offset len : Nat) (fin : Bool)
  | control (f : Frame)

structure SpaceState where
  /-- The write keys and the next packet number. -/
  sealer : Sealer := Sealer.init
  largestRecv : Option Nat := none
  largestRecvTime : Nat := 0
  /-- Received packet numbers as inclusive ranges, largest first. -/
  recvRanges : List (Nat × Nat) := []
  /-- An acknowledgment is due now. -/
  ackPending : Bool := false
  /-- Ack-eliciting packets received since the last acknowledgment sent. -/
  unackedEliciting : Nat := 0
  /-- When a delayed acknowledgment is due (RFC 9000 §13.2.1). -/
  ackDeadline : Option Nat := none
  largestAcked : Option Nat := none
  sent : Std.HashMap Nat (Array Sent) := {}
  cryptoSend : Buffers.Send := Buffers.Send.init
  cryptoRecv : Buffers.Recv := Buffers.Recv.initCrypto cryptoCap
  readKeys : Option Keys := none
  discarded : Bool := false

def SpaceState.nextPn (s : SpaceState) : Nat := s.sealer.nextPn
def SpaceState.writeKeys (s : SpaceState) : Option Keys := s.sealer.keys

/-- Add `pn` to inclusive ranges kept largest first, merging neighbours; at most 32 ranges. -/
def addRange (rs : List (Nat × Nat)) (pn : Nat) : List (Nat × Nat) :=
  let rec go : List (Nat × Nat) → List (Nat × Nat)
    | [] => [(pn, pn)]
    | (lo, hi) :: rest =>
      if pn > hi + 1 then (pn, pn) :: (lo, hi) :: rest
      else if pn + 1 ≥ lo then
        let lo' := min lo pn
        let hi' := max hi pn
        match rest with
        | (lo2, hi2) :: rest' => if lo' ≤ hi2 + 1 then (min lo2 lo', hi') :: rest' else (lo', hi') :: rest
        | [] => [(lo', hi')]
      else (lo, hi) :: go rest
  (go rs).take 32

def containsPn (rs : List (Nat × Nat)) (pn : Nat) : Bool := rs.any fun (lo, hi) => lo ≤ pn && pn ≤ hi

structure Stream where
  send : Buffers.Send := Buffers.Send.init
  recv : Buffers.Recv
  /-- The peer's limit on what we may send. -/
  sendLimit : Nat
  /-- The limit we last advertised for what the peer may send. -/
  advertised : Nat

inductive Phase where
  | handshaking
  | established
  /-- Our CONNECTION_CLOSE is queued or sent; done at the deadline. -/
  | closing (deadline : Nat) (frame : Frame) (sent : Bool)
  | draining (deadline : Nat)
  | closed

structure Config where
  idleTimeout : Nat := 30000
  maxData : Nat := 16 * 1024 * 1024
  maxStreamData : Nat := 4 * 1024 * 1024
  maxStreamsBidi : Nat := 100
  /-- How long we may delay an acknowledgment, in milliseconds (`max_ack_delay`). -/
  maxAckDelay : Nat := 25

structure Conn where
  isClient : Bool
  config : Config
  tls : Tls
  localCid : ByteArray
  remoteCid : ByteArray
  /-- The Destination Connection ID of the client's first Initial. -/
  originalDcid : ByteArray
  retrySource : Option ByteArray := none
  token : ByteArray := ByteArray.empty
  remoteCidSet : Bool := false
  initial : SpaceState := {}
  handshake : SpaceState := {}
  app : SpaceState := {}
  keyPhase : Bool := false
  recovery : Recovery.State
  localParams : TransportParams
  peerParams : Option TransportParams := none
  streams : Std.HashMap Nat Stream := {}
  /-- Peer-initiated streams the application has not yet been told of. -/
  incoming : Array Nat := #[]
  nextLocalStream : Nat
  /-- Peer-initiated bidirectional streams opened so far; lower numbers are open or closed. -/
  peerStreamsOpened : Nat := 0
  peerMaxStreams : Nat := 0
  localMaxStreams : Nat
  peerMaxData : Nat := 0
  dataSent : Nat := 0
  localMaxData : Nat
  dataRead : Nat := 0
  dataRecvHighest : Nat := 0
  pendingControl : Array Frame := #[]
  handshakeConfirmed : Bool := false
  handshakeDonePending : Bool := false
  addressValidated : Bool
  bytesRecv : Nat := 0
  bytesSent : Nat := 0
  /-- Ack-eliciting packets received, and ACK frames sent. -/
  elicitingRecv : Nat := 0
  acksSent : Nat := 0
  idleDeadline : Option Nat := none
  probe : Option (Space × Nat) := none
  phase : Phase := .handshaking
  /-- Why the connection closed: our error, or the peer's close code. -/
  closeReason : Option (Bool × Nat × String) := none

namespace Conn

def space (c : Conn) : Space → SpaceState
  | .initial => c.initial
  | .handshake => c.handshake
  | .application => c.app

def setSpace (c : Conn) : Space → SpaceState → Conn
  | .initial, s => { c with initial := s }
  | .handshake, s => { c with handshake := s }
  | .application, s => { c with app := s }

def modifySpace (c : Conn) (sp : Space) (f : SpaceState → SpaceState) : Conn :=
  c.setSpace sp (f (c.space sp))

def isEstablished (c : Conn) : Bool := match c.phase with | .established => true | _ => false
def isClosed (c : Conn) : Bool := match c.phase with | .closed => true | _ => false

def idleTimeoutUs (c : Conn) : Nat :=
  let peer := (c.peerParams.map (·.maxIdleTimeout)).getD 0
  let ms := if peer == 0 then c.config.idleTimeout
    else if c.config.idleTimeout == 0 then peer else min peer c.config.idleTimeout
  ms * 1000

def localTransportParams (cfg : Config) (isClient : Bool) (localCid originalDcid : ByteArray)
    (retrySource : Option ByteArray) : TransportParams :=
  { maxIdleTimeout := cfg.idleTimeout,
    initialMaxData := cfg.maxData,
    initialMaxStreamDataBidiLocal := cfg.maxStreamData,
    initialMaxStreamDataBidiRemote := cfg.maxStreamData,
    initialMaxStreamDataUni := 0,
    initialMaxStreamsBidi := cfg.maxStreamsBidi,
    initialMaxStreamsUni := 0,
    maxAckDelay := cfg.maxAckDelay,
    activeConnectionIdLimit := 2,
    initialSourceConnectionId := some localCid,
    originalDestinationConnectionId := if isClient then none else some originalDcid,
    retrySourceConnectionId := if isClient then none else retrySource }

/-- Close with an error: a CONNECTION_CLOSE goes out, then the connection waits out three PTOs. -/
def fail (c : Conn) (now : Nat) (e : TransportError) (reason : String := "") : Conn :=
  match c.phase with
  | .closing .. | .draining _ | .closed => c
  | _ =>
    let deadline := now + 3 * c.recovery.ptoDuration .initial
    { c with phase := .closing deadline (.connectionClose false e.code 0 reason.toUTF8) false,
             closeReason := some (true, e.code, reason) }

/-- Close by the application, with no error. -/
def close (c : Conn) (now : Nat) : Conn :=
  match c.phase with
  | .closing .. | .draining _ | .closed => c
  | _ =>
    let deadline := now + 3 * c.recovery.ptoDuration .application
    { c with phase := .closing deadline (.connectionClose c.isEstablished 0 0 ByteArray.empty) false,
             closeReason := some (true, 0, "") }

/-- Install the secrets TLS produced for a level. -/
def install (c : Conn) (level : Level) (suite : Suite) (s : Secrets) : Conn :=
  c.modifySpace (Space.ofLevel level) fun sp =>
    { sp with readKeys := some (Keys.ofSecret suite s.read),
              sealer := sp.sealer.rekey (Keys.ofSecret suite s.write) }

def discardSpace (c : Conn) (sp : Space) : Conn :=
  if (c.space sp).discarded then c else
  let c := c.modifySpace sp fun s =>
    { s with readKeys := none, sealer := s.sealer.discard, discarded := true, sent := {}, ackPending := false,
             cryptoSend := Buffers.Send.init }
  { c with recovery := c.recovery.discardSpace sp }

/-- The peer's transport parameters, checked against the connection IDs (RFC 9000 §7.3). -/
def acceptPeerParams (c : Conn) (now : Nat) (raw : ByteArray) : Conn :=
  match TransportParams.decode raw with
  | none => c.fail now .transportParameter "malformed transport parameters"
  | some p =>
    let cidOk :=
      p.initialSourceConnectionId == some c.remoteCid &&
      (!c.isClient || (p.originalDestinationConnectionId == some c.originalDcid &&
        p.retrySourceConnectionId == c.retrySource))
    if !cidOk then c.fail now .transportParameter "connection ID mismatch"
    else
      { c with peerParams := some p, peerMaxData := p.initialMaxData,
               peerMaxStreams := p.initialMaxStreamsBidi,
               recovery := c.recovery.setMaxAckDelay (p.maxAckDelay * 1000) }

/-- Feed CRYPTO bytes that became contiguous at a level to TLS, and act on its outputs. -/
def feedTls (c : Conn) (now : Nat) (level : Level) (data : ByteArray) : Conn :=
  if data.size == 0 then c else
  match c.tls.recv level data with
  | .error a => c.fail now (.crypto a) "TLS handshake failed"
  | .ok (tls, outs) => Id.run do
    let mut c := { c with tls }
    for o in outs do
      match o with
      | .send l d => c := c.modifySpace (Space.ofLevel l) fun sp => { sp with cryptoSend := sp.cryptoSend.write d }
      | .install l suite s => c := c.install l suite s
    if c.peerParams.isNone then
      if let some raw := c.tls.established? then
        c := c.acceptPeerParams now raw
        if !c.isClosed && (match c.phase with | .handshaking => true | _ => false) then
          c := { c with phase := .established }
          if !c.isClient then
            -- The server's handshake is confirmed once complete (RFC 9001 §4.1.2).
            c := { c with handshakeConfirmed := true, handshakeDonePending := true,
                          recovery := c.recovery.setHandshakeConfirmed }
            c := c.discardSpace .handshake
    pure c

def streamLimitFor (c : Conn) (id : Nat) : Nat :=
  match c.peerParams with
  | none => 0
  | some p =>
    let localInitiated := (id % 2 == 0) == c.isClient
    if localInitiated then p.initialMaxStreamDataBidiRemote else p.initialMaxStreamDataBidiLocal

/-- The stream a peer's frame refers to, created if new; `none` for one already closed, whose
late or duplicated frames are ignored. -/
def peerStream (c : Conn) (id : Nat) : Except (TransportError × String) (Conn × Option Stream) := do
  if let some s := c.streams[id]? then return (c, some s)
  if id % 4 >= 2 then throw (.streamState, "unidirectional stream")
  let localInitiated := (id % 2 == 0) == c.isClient
  if localInitiated then
    if id < c.nextLocalStream then return (c, none)
    throw (.streamState, "unopened local stream")
  if id / 4 < c.peerStreamsOpened then return (c, none)
  if id / 4 >= c.localMaxStreams then throw (.streamLimit, "stream limit")
  -- Lower-numbered peer streams open implicitly (RFC 9000 §3.2).
  let mut c := c
  for n in [c.peerStreamsOpened:id / 4 + 1] do
    let sid := 4 * n + (if c.isClient then 1 else 0)
    let s : Stream := { recv := Buffers.Recv.init c.config.maxStreamData, sendLimit := c.streamLimitFor sid,
                        advertised := c.config.maxStreamData }
    c := { c with streams := c.streams.insert sid s, incoming := c.incoming.push sid }
  c := { c with peerStreamsOpened := id / 4 + 1 }
  pure (c, c.streams[id]?)

def onStreamFrame (c : Conn) (id offset : Nat) (data : ByteArray) (fin : Bool) : Except (TransportError × String) Conn := do
  let (c, some s) ← c.peerStream id | return c
  let before := s.recv.highestOffset
  let recv ← match s.recv.insert offset data fin with
    | .ok r => pure r
    | .error .flowControl => throw (.flowControl, "stream flow control")
    | .error .finalSize => throw (.finalSize, "final size")
    | .error .bufferExceeded => throw (.flowControl, "stream buffer")
  let grown := recv.highestOffset - before
  let total := c.dataRecvHighest + grown
  if total > c.localMaxData then throw (.flowControl, "connection flow control")
  pure { c with streams := c.streams.insert id { s with recv }, dataRecvHighest := total }

/-- Acknowledged or lost: the frames a packet carried. -/
def onSentFate (c : Conn) (acked : Bool) (items : Array Sent) : Conn := Id.run do
  let mut c := c
  for it in items do
    match it with
    | .crypto l off len =>
      c := c.modifySpace (Space.ofLevel l) fun sp =>
        { sp with cryptoSend := if acked then sp.cryptoSend.onAcked off len false
                                else sp.cryptoSend.onLost off len false }
    | .stream id off len fin =>
      if let some s := c.streams[id]? then
        let send := if acked then s.send.onAcked off len fin else s.send.onLost off len fin
        c := { c with streams := c.streams.insert id { s with send } }
    | .control f =>
      if !acked then
        match f with
        | .handshakeDone => c := { c with handshakeDonePending := true }
        | .maxData _ => c := { c with pendingControl := c.pendingControl.push (.maxData c.localMaxData) }
        | .maxStreamData id _ =>
          if let some s := c.streams[id]? then
            c := { c with pendingControl := c.pendingControl.push (.maxStreamData id s.advertised) }
        | .maxStreams b _ => c := { c with pendingControl := c.pendingControl.push (.maxStreams b c.localMaxStreams) }
        | f => c := { c with pendingControl := c.pendingControl.push f }
  pure c

def takeSent (c : Conn) (sp : Space) (pn : Nat) : Conn × Array Sent :=
  let s := c.space sp
  ((c.setSpace sp { s with sent := s.sent.erase pn }), s.sent.getD pn #[])

def onAck (c : Conn) (now : Nat) (sp : Space) (ranges : List (Nat × Nat)) (delay : Nat) :
    Except (TransportError × String) Conn := do
  let largest := (ranges.map (·.2)).foldl max 0
  if largest ≥ (c.space sp).nextPn then throw (.protocolViolation, s!"ack of unsent packet {largest} in {repr sp}")
  let delayUs := if sp == .application then
    delay * 2 ^ ((c.peerParams.map (·.ackDelayExponent)).getD 3) else 0
  let (rec, res) := c.recovery.onAckReceived sp ranges delayUs now
  let mut c := { c with recovery := rec }
  c := c.modifySpace sp fun s => { s with largestAcked := some (max largest (s.largestAcked.getD 0)) }
  for pn in res.acked do
    let (c', items) := c.takeSent sp pn
    c := c'.onSentFate true items
  for (lsp, pn) in res.lost do
    let (c', items) := c.takeSent lsp pn
    c := c'.onSentFate false items
  if c.isClient && sp == Space.handshake then
    c := { c with recovery := c.recovery.setPeerCompletedAddressValidation }
  pure c

def onFrame (c : Conn) (now : Nat) (sp : Space) (f : Frame) : Except (TransportError × String) Conn := do
  if sp != .application && !f.allowedBeforeOneRtt then throw (.protocolViolation, "frame not allowed at this level")
  match f with
  | .padding _ | .ping => pure c
  | .ack ranges delay => c.onAck now sp ranges delay
  | .crypto off data =>
    let s := c.space sp
    let recv ← match s.cryptoRecv.insert off data false with
      | .ok r => pure r
      | .error _ => throw (.cryptoBufferExceeded, "crypto buffer")
    let (recv, bytes) := recv.read recv.readable
    let c := c.setSpace sp { s with cryptoRecv := recv }
    pure (c.feedTls now sp.level bytes)
  | .stream id off data fin =>
    if c.tls.established?.isNone then throw (.protocolViolation, "stream data before the handshake completed")
    c.onStreamFrame id off data fin
  | .maxData m => pure { c with peerMaxData := max c.peerMaxData m }
  | .maxStreamData id m =>
    match c.streams[id]? with
    | some s => pure { c with streams := c.streams.insert id { s with sendLimit := max s.sendLimit m } }
    | none => pure c
  | .maxStreams true m => pure { c with peerMaxStreams := max c.peerMaxStreams m }
  | .pathChallenge d => pure { c with pendingControl := c.pendingControl.push (.pathResponse d) }
  | .connectionClose app code _ reason =>
    let deadline := now + 3 * c.recovery.ptoDuration .application
    pure { c with phase := .draining deadline,
                  closeReason := some (false, code, String.fromUTF8! (if reason.validateUTF8 then reason else ByteArray.empty) ++ (if app then " (application)" else "")) }
  | .handshakeDone =>
    if !c.isClient then throw (.protocolViolation, "HANDSHAKE_DONE from a client")
    let c := { c with handshakeConfirmed := true, recovery := c.recovery.setHandshakeConfirmed.setPeerCompletedAddressValidation }
    pure (c.discardSpace .handshake)
  | _ => pure c

/-- Process one packet already opened. -/
def onPacket (c : Conn) (now : Nat) (sp : Space) (pn : Nat) (payload : ByteArray) : Conn :=
  if containsPn (c.space sp).recvRanges pn then c else
  match Frame.parseAll payload with
  | none => c.fail now .frameEncoding "malformed frames"
  | some frames => Id.run do
    let mut c := c
    for f in frames do
      match c.onFrame now sp f with
      | .ok c' => c := c'
      | .error (e, why) => return c.fail now e why
      if c.isClosed then return c
    let eliciting := frames.any (·.ackEliciting)
    -- RFC 9000 §13.2: Initial and Handshake packets, and packets out of order or after a gap, are
    -- acknowledged at once; other 1-RTT packets every second one, or after `max_ack_delay`.
    let s := c.space sp
    let inOrder := match s.largestRecv with | some l => pn == l + 1 | none => true
    let count := if eliciting then s.unackedEliciting + 1 else s.unackedEliciting
    let ackNow := eliciting && (sp != .application || !inOrder || count ≥ 2)
    let delayUntil := now + c.config.maxAckDelay * 1000
    c := c.setSpace sp
      { s with recvRanges := addRange s.recvRanges pn,
               largestRecv := some (max pn (s.largestRecv.getD 0)),
               largestRecvTime := if pn ≥ s.largestRecv.getD 0 then now else s.largestRecvTime,
               ackPending := s.ackPending || ackNow,
               unackedEliciting := count,
               ackDeadline := if eliciting && !ackNow then
                 some (min delayUntil (s.ackDeadline.getD delayUntil)) else s.ackDeadline }
    pure { c with idleDeadline := some (now + c.idleTimeoutUs),
                  elicitingRecv := c.elicitingRecv + (if eliciting then 1 else 0) }

/-- The client's response to a Retry (RFC 9000 §17.2.5.2): new Initial keys and the token, and the
ClientHello again. -/
def onRetry (c : Conn) (now : Nat) (scid token pkt : ByteArray) : Conn :=
  if !c.isClient || c.retrySource.isSome || c.remoteCidSet || token.size == 0 then c
  else if !retryValid c.originalDcid pkt then c
  else
    let (ck, sk) := initialKeys scid
    let s := c.initial
    let sentAll := s.cryptoSend.sentOffset
    let c := { c with remoteCid := scid, retrySource := some scid, token,
                      recovery := c.recovery.discardSpace .initial }
    let _ := now
    c.setSpace .initial { s with sealer := s.sealer.rekey ck, readKeys := some sk, sent := {},
                                 cryptoSend := s.cryptoSend.onLost 0 sentAll false }

/-- A datagram from the peer. -/
def recv (c : Conn) (now : Nat) (dgram : ByteArray) : Conn := Id.run do
  match c.phase with
  | .closed | .draining _ => return c
  | _ => pure ()
  let mut c := { c with bytesRecv := c.bytesRecv + dgram.size }
  let mut pos := 0
  for _ in [0:8] do
    if pos ≥ dgram.size || c.isClosed then break
    let some (hdr, len) := parseHeader dgram pos c.localCid.size | break
    let pkt := dgram.extract pos (pos + len)
    pos := pos + len
    match hdr with
    | .versionNegotiation .. => pure ()
    | .long .retry _ dcid scid token _ =>
      if dcid == c.localCid then c := c.onRetry now scid token pkt
    | .long typ version dcid scid _ pnOffset =>
      if version != version1 || dcid != c.localCid && !(typ == .initial && dcid == c.originalDcid) then
        continue
      let sp : Space := if typ == .handshake then .handshake else .initial
      if typ == .zeroRtt then continue
      let some keys := (c.space sp).readKeys | continue
      let some o := openPacket keys true pkt pnOffset (c.space sp).largestRecv | continue
      if o.firstByte &&& 0x0c != 0 then
        c := c.fail now .protocolViolation "reserved bits"
        continue
      if c.isClient && !c.remoteCidSet then
        c := { c with remoteCid := scid, remoteCidSet := true }
      if !c.isClient && sp == .handshake then
        c := { c with addressValidated := true }
        c := c.discardSpace .initial
      c := c.onPacket now sp o.pn o.payload
    | .short dcid pnOffset =>
      if dcid != c.localCid then continue
      -- A server processes no 1-RTT packet before its handshake completes (RFC 9001 §5.7).
      if !c.isClient && c.tls.established?.isNone then continue
      let some keys := c.app.readKeys | continue
      match openPacket keys false pkt pnOffset c.app.largestRecv with
      | some o =>
        if o.firstByte &&& 0x18 != 0 then
          c := c.fail now .protocolViolation "reserved bits"
          continue
        if (o.firstByte &&& 0x04 != 0) != c.keyPhase then continue
        c := c.onPacket now .application o.pn o.payload
      | none =>
        -- The peer may have updated its keys (RFC 9001 §6.2).
        if let some wk := c.app.writeKeys then
          let nk := keys.next
          if let some o := openPacket nk false pkt pnOffset c.app.largestRecv then
            if (o.firstByte &&& 0x04 != 0) != c.keyPhase then
              c := c.modifySpace .application fun s => { s with readKeys := some nk, sealer := s.sealer.rekey wk.next }
              c := { c with keyPhase := !c.keyPhase }
              c := c.onPacket now .application o.pn o.payload
  pure c

/-! ## Sending -/

/-- Bytes the server may still send before the client's address is validated (RFC 9000 §8.1). -/
def amplificationAllowance (c : Conn) : Nat :=
  if c.isClient || c.addressValidated then maxDatagram else 3 * c.bytesRecv - min (3 * c.bytesRecv) c.bytesSent

def ackFrame (s : SpaceState) (now : Nat) (sp : Space) : Option Frame :=
  if s.recvRanges.isEmpty then none else
  let delay := if sp == .application then (now - s.largestRecvTime) / 8 else 0
  some (.ack s.recvRanges delay)

/-- An acknowledgment went out: nothing is pending until the next ack-eliciting packet. -/
def ackSent (c : Conn) (sp : Space) : Conn :=
  { c.modifySpace sp (fun s => { s with ackPending := false, unackedEliciting := 0, ackDeadline := none })
    with acksSent := c.acksSent + 1 }

structure Built where
  frames : Array Frame := #[]
  sent : Array Sent := #[]
  size : Nat := 0
  eliciting : Bool := false

def Built.add (b : Built) (f : Frame) (s : Option Sent := none) : Built :=
  { b with frames := b.frames.push f, size := b.size + f.encode.size,
           sent := match s with | some x => b.sent.push x | none => b.sent,
           eliciting := b.eliciting || f.ackEliciting }

/-- The frames for one packet in a space, within `budget` payload bytes. `allowData` is false when
congestion control forbids anything but acknowledgments. -/
def buildFrames (c : Conn) (now : Nat) (sp : Space) (budget : Nat) (allowData : Bool) :
    Conn × Built := Id.run do
  let mut b : Built := {}
  let mut c := c
  let s := c.space sp
  if s.ackPending || (allowData && s.recvRanges.length > 0 && c.probe.isSome) then
    if let some f := ackFrame s now sp then
      if f.encode.size ≤ budget then
        b := b.add f
        c := c.ackSent sp
  if !allowData then return (c, b)
  if let .closing _ _ _ := c.phase then return (c, b)
  -- CRYPTO
  for _ in [0:16] do
    let room := budget - min budget (b.size + 8)
    if room == 0 then break
    let sp' := c.space sp
    let (chunk, send) := sp'.cryptoSend.next room (2 ^ 62)
    match chunk with
    | none => break
    | some (off, data, _) =>
      if data.size == 0 then break
      c := c.setSpace sp { sp' with cryptoSend := send }
      b := b.add (.crypto off data) (some (.crypto sp.level off data.size))
  if sp == .application && c.isEstablished then
    if c.handshakeDonePending && b.size + 1 ≤ budget then
      b := b.add .handshakeDone (some (.control .handshakeDone))
      c := { c with handshakeDonePending := false }
    let mut kept := #[]
    for f in c.pendingControl do
      if b.size + f.encode.size ≤ budget then b := b.add f (some (.control f))
      else kept := kept.push f
    c := { c with pendingControl := kept }
    -- STREAM frames, lowest stream first.
    let ids := (c.streams.toList.map (·.1)).toArray.qsort (· < ·)
    for id in ids do
      for _ in [0:64] do
        let some st := c.streams[id]? | break
        let overhead := Frame.streamOverhead id st.send.sentOffset 1200 + 1
        if b.size + overhead ≥ budget then break
        let room := budget - b.size - overhead
        let connRoom := c.peerMaxData - min c.peerMaxData c.dataSent
        let limit := min st.sendLimit (st.send.sentOffset + connRoom)
        let before := st.send.sentOffset
        let (chunk, send) := st.send.next room limit
        match chunk with
        | none => break
        | some (off, data, fin) =>
          c := { c with streams := c.streams.insert id { st with send },
                        dataSent := c.dataSent + (send.sentOffset - before) }
          b := b.add (.stream id off data fin) (some (.stream id off data.size fin))
  if c.probe.isSome && !b.eliciting && b.size + 1 ≤ budget then
    b := b.add .ping
  -- A delayed acknowledgment rides along with anything else being sent.
  if b.eliciting && (c.space sp).unackedEliciting > 0 then
    if let some f := ackFrame (c.space sp) now sp then
      if b.size + f.encode.size ≤ budget then
        b := b.add f
        c := c.ackSent sp
  pure (c, b)

/-- Header bytes for a packet in a space, its packet number length included. -/
def headerFor (c : Conn) (sp : Space) (pn pnLen payloadLen : Nat) : ByteArray :=
  match sp with
  | .initial => longHeader .initial c.remoteCid c.localCid (if c.isClient then c.token else ByteArray.empty)
      pn pnLen payloadLen
  | .handshake => longHeader .handshake c.remoteCid c.localCid ByteArray.empty pn pnLen payloadLen
  | .application => shortHeader c.remoteCid c.keyPhase pn pnLen

/-- Seal a packet from built frames with the space's sealer; with `target` nonzero, padded to
exactly `target` bytes. A space out of packet numbers closes the connection. -/
def sealPacket (c : Conn) (now : Nat) (sp : Space) (b : Built) (target : Nat) :
    Conn × ByteArray :=
  let s := c.space sp
  let frames := b.frames.foldl (fun acc f => acc ++ f.encode) ByteArray.empty
  let build (pn : Nat) : ByteArray × Nat × ByteArray :=
    let pnLen := pnLength pn s.largestAcked
    -- The header's size does not depend on the payload's: Length is always two bytes.
    let hdrSize := (c.headerFor sp pn pnLen 0).size
    let minPayload := max (target - min target (hdrSize + tagSize)) (4 - min 4 pnLen)
    let payload := if frames.size < minPayload then
      frames ++ ⟨Array.replicate (minPayload - frames.size) 0⟩ else frames
    (c.headerFor sp pn pnLen payload.size, pnLen, payload)
  match s.sealer.send (sp != .application) build with
  | none =>
    ({ c with phase := .closed, closeReason := c.closeReason <|> some (true, 0, "packet numbers exhausted") },
     ByteArray.empty)
  | some (sealer, pn, pkt) =>
    let inFlight := b.eliciting || target > 0
    let sent := if b.sent.isEmpty && !b.eliciting then s.sent else s.sent.insert pn b.sent
    let c := c.setSpace sp { s with sealer, sent }
    let record : Recovery.SentPacket :=
      { pn, timeSent := now, ackEliciting := b.eliciting, inFlight, size := pkt.size }
    ({ c with recovery := c.recovery.onPacketSent sp record }, pkt)

def headerOverhead (c : Conn) (sp : Space) : Nat :=
  match sp with
  | .initial => 1 + 4 + 1 + c.remoteCid.size + 1 + c.localCid.size +
      (if c.isClient then varIntLen c.token.size + c.token.size else 1) + 2 + 4
  | .handshake => 1 + 4 + 1 + c.remoteCid.size + 1 + c.localCid.size + 2 + 4
  | .application => 1 + c.remoteCid.size + 4

/-- The next datagram to send, if any. -/
def poll (c : Conn) (now : Nat) : Conn × Option ByteArray := Id.run do
  match c.phase with
  | .closed | .draining _ => return (c, none)
  | .closing d f sent =>
    if sent then return (c, none)
    let sp : Space := if c.app.writeKeys.isSome && c.isEstablished then .application
      else if c.handshake.writeKeys.isSome then .handshake else .initial
    if (c.space sp).writeKeys.isNone then return ({ c with phase := .closing d f true }, none)
    let f := match f, sp with
      | .connectionClose true _ _ _, .application => f
      | .connectionClose _ code ft r, _ => .connectionClose false code ft r
      | _, _ => f
    let (c, pkt) := c.sealPacket now sp (Built.add {} f) 0
    if c.isClosed then return (c, none)
    return ({ c with phase := .closing d f true }, some pkt)
  | _ => pure ()
  let mut c := c
  let limit := min maxDatagram c.amplificationAllowance
  let cwndOk := c.recovery.sendAllowance ≥ maxDatagram || c.probe.isSome
  -- First the frames of each packet, then the packets, so the last can pad the datagram.
  let mut parts : Array (Space × Built) := #[]
  let mut used := 0
  for sp in [Space.initial, .handshake, .application] do
    if (c.space sp).writeKeys.isNone || (c.space sp).discarded then continue
    let overhead := c.headerOverhead sp + tagSize
    if used + overhead + 8 > limit then continue
    let budget := limit - used - overhead
    let probeHere := match c.probe with | some (psp, _) => psp == sp | none => false
    let c0 := if probeHere || c.probe.isNone then c else { c with probe := none }
    let (c1, b) := c0.buildFrames now sp budget cwndOk
    c := if probeHere || c.probe.isNone then c1 else { c1 with probe := c.probe }
    if b.frames.isEmpty then continue
    parts := parts.push (sp, b)
    used := used + overhead + b.size
    if probeHere then
      c := { c with probe := match c.probe with
        | some (psp, n) => if n > 1 then some (psp, n - 1) else none
        | none => none }
  if parts.isEmpty then return (c, none)
  -- A client pads every datagram with an Initial in it, a server those with an ack-eliciting
  -- Initial, to 1200 bytes (RFC 9000 §14.1).
  let pad := parts.any fun (sp, b) => sp == .initial && (c.isClient || b.eliciting)
  let mut dgram := ByteArray.empty
  for h : i in [0:parts.size] do
    let (sp, b) := parts[i]
    let target := if pad && i + 1 == parts.size then limit - min limit dgram.size else 0
    let (c', pkt) := c.sealPacket now sp b target
    c := c'
    if c.isClosed then return (c, none)
    dgram := dgram ++ pkt
    -- The client drops Initial keys once it sends a Handshake packet (RFC 9001 §4.9.1).
    if c.isClient && sp == .handshake then c := c.discardSpace .initial
  pure ({ c with bytesSent := c.bytesSent + dgram.size }, some dgram)

/-! ## Timers -/

def closeDeadline (c : Conn) : Option Nat :=
  match c.phase with
  | .closing d _ _ => some d
  | .draining d => some d
  | _ => none

def nextTimeout (c : Conn) : Option Nat :=
  if c.isClosed then none else
  [c.recovery.lossDetectionDeadline, c.idleDeadline, c.closeDeadline, c.app.ackDeadline].filterMap id |>.foldl
    (fun acc d => some (match acc with | some a => min a d | none => d)) none

def onTimeout (c : Conn) (now : Nat) : Conn := Id.run do
  if let some d := c.closeDeadline then
    if now ≥ d then return { c with phase := .closed }
  if let some d := c.idleDeadline then
    if now ≥ d then return { c with phase := .closed, closeReason := c.closeReason <|> some (true, 0, "idle timeout") }
  let c := match c.app.ackDeadline with
    | some d => if now ≥ d then c.modifySpace .application fun s =>
        { s with ackPending := true, ackDeadline := none } else c
    | none => c
  match c.recovery.lossDetectionDeadline with
  | some d =>
    if now < d then return c
    let (rec, res) := c.recovery.onLossDetectionTimeout now
    let mut c := { c with recovery := rec }
    for (sp, pn) in res.lost do
      let (c', items) := c.takeSent sp pn
      c := c'.onSentFate false items
    if let some (sp, n) := res.probe then
      -- Probe with a level that has keys; requeue its unacknowledged data with the probe.
      let sp := if (c.space sp).writeKeys.isSome && !(c.space sp).discarded then sp
        else if c.handshake.writeKeys.isSome && !c.handshake.discarded then .handshake else .initial
      let s := c.space sp
      let mut c' := c
      for (_, items) in s.sent.toList do
        c' := c'.onSentFate false items
      c := { c' with probe := some (sp, n) }
    pure c
  | none => pure c

/-! ## The application side -/

/-- Open a bidirectional stream, if the peer's limit allows. -/
def openStream (c : Conn) : Conn × Option Nat :=
  let id := c.nextLocalStream
  if !c.isEstablished || id / 4 ≥ c.peerMaxStreams then (c, none) else
  let s : Stream := { recv := Buffers.Recv.init c.config.maxStreamData, sendLimit := c.streamLimitFor id,
                      advertised := c.config.maxStreamData }
  ({ c with streams := c.streams.insert id s, nextLocalStream := id + 4 }, some id)

def write (c : Conn) (id : Nat) (data : ByteArray) : Conn :=
  match c.streams[id]? with
  | some s => { c with streams := c.streams.insert id { s with send := s.send.write data } }
  | none => c

def finish (c : Conn) (id : Nat) : Conn :=
  match c.streams[id]? with
  | some s => { c with streams := c.streams.insert id { s with send := s.send.finish } }
  | none => c

/-- Read up to `max` bytes; raises the peer's credit as data is consumed. -/
def read (c : Conn) (id : Nat) (max : Nat) : Conn × ByteArray := Id.run do
  let some s := c.streams[id]? | return (c, ByteArray.empty)
  let (recv, data) := s.recv.read max
  let mut s := { s with recv }
  let mut c := { c with dataRead := c.dataRead + data.size }
  let window := c.config.maxStreamData
  if recv.finalSize.isNone && recv.readOffset + window / 2 ≥ s.advertised then
    let lim := recv.readOffset + window
    s := { s with recv := s.recv.setLimit lim, advertised := lim }
    c := { c with pendingControl := c.pendingControl.push (.maxStreamData id lim) }
  if c.dataRead + c.config.maxData / 2 ≥ c.localMaxData then
    let lim := c.dataRead + c.config.maxData
    c := { c with localMaxData := lim, pendingControl := c.pendingControl.push (.maxData lim) }
  pure ({ c with streams := c.streams.insert id s }, data)

def readable (c : Conn) (id : Nat) : Nat := (c.streams[id]?.map (·.recv.readable)).getD 0

/-- The peer finished the stream and everything it sent has been read. -/
def recvFinished (c : Conn) (id : Nat) : Bool := (c.streams[id]?.map (·.recv.isFinished)).getD false

/-- The peer finished the stream and all of it has arrived, read or not. -/
def recvComplete (c : Conn) (id : Nat) : Bool :=
  match c.streams[id]? with
  | some s => s.recv.finalSize == some (s.recv.readOffset + s.recv.readable)
  | none => false

def sendFinished (c : Conn) (id : Nat) : Bool := (c.streams[id]?.map (·.send.isAllAcked)).getD false

/-- Forget a stream both sides are done with; a peer stream frees a slot for another. -/
def retire (c : Conn) (id : Nat) : Conn :=
  if !(c.recvFinished id && c.sendFinished id) then c else
  let c := { c with streams := c.streams.erase id }
  let peerInitiated := (id % 2 == 0) != c.isClient
  if peerInitiated then
    let m := c.localMaxStreams + 1
    { c with localMaxStreams := m, pendingControl := c.pendingControl.push (.maxStreams true m) }
  else c

def takeIncoming (c : Conn) : Conn × Array Nat := ({ c with incoming := #[] }, c.incoming)

/-! ## Creating connections -/

def newClient (cfg : Config) (tlsCfg : LeanTLS.Handshake.Client.Config) (seed : Vector UInt8 32)
    (localCid dcid : ByteArray) (now : Nat) : Except LeanTLS.Alert Conn := do
  let params := localTransportParams cfg true localCid dcid none
  let tlsCfg := { tlsCfg with transportParams := params.encode }
  let (st, outs) ← LeanTLS.Handshake.Client.start tlsCfg seed
  let (ck, sk) := initialKeys dcid
  let mut c : Conn :=
    { isClient := true, config := cfg, tls := .client tlsCfg st, localCid, remoteCid := dcid,
      originalDcid := dcid, recovery := Recovery.init true maxDatagram, localParams := params,
      nextLocalStream := 0, localMaxStreams := cfg.maxStreamsBidi, localMaxData := cfg.maxData,
      addressValidated := true, idleDeadline := some (now + cfg.idleTimeout * 1000) }
  c := c.setSpace .initial { c.initial with sealer := c.initial.sealer.rekey ck, readKeys := some sk }
  for o in outs do
    if let .send l d := o then
      c := c.modifySpace (Space.ofLevel l) fun sp => { sp with cryptoSend := sp.cryptoSend.write d }
  pure c

/-- A server connection for a client's first Initial, addressed to `odcid`. After a Retry the
client's Initial is addressed to `retrySource`, the connection ID the Retry gave it, and the
client's address is already validated by the token. -/
def newServer (cfg : Config) (tlsCfg : LeanTLS.Handshake.Server.Config) (seed : Vector UInt8 32)
    (localCid odcid peerCid : ByteArray) (now : Nat) (retrySource : Option ByteArray := none) : Conn :=
  let params := localTransportParams cfg false localCid odcid retrySource
  let tlsCfg := { tlsCfg with transportParams := params.encode }
  let (sk, ck) := initialKeys (retrySource.getD odcid)
  let c : Conn :=
    { isClient := false, config := cfg, tls := .server tlsCfg seed LeanTLS.Handshake.Server.init,
      localCid, remoteCid := peerCid, remoteCidSet := true, originalDcid := retrySource.getD odcid,
      retrySource, recovery := (Recovery.init false maxDatagram).setPeerCompletedAddressValidation,
      localParams := params, nextLocalStream := 1, localMaxStreams := cfg.maxStreamsBidi,
      localMaxData := cfg.maxData, addressValidated := retrySource.isSome,
      idleDeadline := some (now + cfg.idleTimeout * 1000) }
  c.setSpace .initial { c.initial with sealer := c.initial.sealer.rekey ck, readKeys := some sk }

end Conn

end LeanQUIC
