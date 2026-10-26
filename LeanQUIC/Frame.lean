/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import LeanQUIC.VarInt

namespace LeanQUIC

open LeanTLS.Wire

/-! # Frames (RFC 9000 §19)

A packet's payload is a sequence of frames. ACK ranges are kept as inclusive
`(smallest, largest)` pairs, largest first. -/

inductive Frame where
  | padding (count : Nat)
  | ping
  | ack (ranges : List (Nat × Nat)) (delay : Nat)
  | resetStream (id error finalSize : Nat)
  | stopSending (id error : Nat)
  | crypto (offset : Nat) (data : ByteArray)
  | newToken (token : ByteArray)
  | stream (id offset : Nat) (data : ByteArray) (fin : Bool)
  | maxData (max : Nat)
  | maxStreamData (id max : Nat)
  | maxStreams (bidi : Bool) (max : Nat)
  | dataBlocked (limit : Nat)
  | streamDataBlocked (id limit : Nat)
  | streamsBlocked (bidi : Bool) (limit : Nat)
  | newConnectionId (seq retirePriorTo : Nat) (cid resetToken : ByteArray)
  | retireConnectionId (seq : Nat)
  | pathChallenge (data : ByteArray)
  | pathResponse (data : ByteArray)
  | connectionClose (app : Bool) (error frameType : Nat) (reason : ByteArray)
  | handshakeDone
deriving Inhabited

namespace Frame

/-- Whether receiving the frame calls for an acknowledgment (RFC 9000 §13.2). -/
def ackEliciting : Frame → Bool
  | padding _ | ack _ _ | connectionClose _ _ _ _ => false
  | _ => true

/-- Allowed in Initial and Handshake packets (RFC 9000 §12.4). -/
def allowedBeforeOneRtt : Frame → Bool
  | padding _ | ping | ack _ _ | crypto _ _ | connectionClose false _ _ _ => true
  | _ => false

def write : Frame → Writer Unit
  | padding n => Writer.bytes ⟨Array.replicate n 0⟩
  | ping => writeVarInt 0x01
  | ack ranges delay => do
    match ranges with
    | [] => throw .internalError
    | (lo, hi) :: rest =>
      writeVarInt 0x02
      writeVarInt hi
      writeVarInt delay
      writeVarInt rest.length
      writeVarInt (hi - lo)
      let mut prevLo := lo
      for (l, h) in rest do
        writeVarInt (prevLo - h - 2)
        writeVarInt (h - l)
        prevLo := l
  | resetStream id e f => do writeVarInt 0x04; writeVarInt id; writeVarInt e; writeVarInt f
  | stopSending id e => do writeVarInt 0x05; writeVarInt id; writeVarInt e
  | crypto off d => do writeVarInt 0x06; writeVarInt off; writeVarInt d.size; Writer.bytes d
  | newToken t => do writeVarInt 0x07; writeVarInt t.size; Writer.bytes t
  | stream id off d fin => do
    writeVarInt (0x08 ||| (if off != 0 then 0x04 else 0) ||| 0x02 ||| (if fin then 0x01 else 0))
    writeVarInt id
    if off != 0 then writeVarInt off
    writeVarInt d.size
    Writer.bytes d
  | maxData m => do writeVarInt 0x10; writeVarInt m
  | maxStreamData id m => do writeVarInt 0x11; writeVarInt id; writeVarInt m
  | maxStreams b m => do writeVarInt (if b then 0x12 else 0x13); writeVarInt m
  | dataBlocked l => do writeVarInt 0x14; writeVarInt l
  | streamDataBlocked id l => do writeVarInt 0x15; writeVarInt id; writeVarInt l
  | streamsBlocked b l => do writeVarInt (if b then 0x16 else 0x17); writeVarInt l
  | newConnectionId s r cid tok => do
    writeVarInt 0x18; writeVarInt s; writeVarInt r
    Writer.u8 (UInt8.ofNat cid.size); Writer.bytes cid; Writer.bytes tok
  | retireConnectionId s => do writeVarInt 0x19; writeVarInt s
  | pathChallenge d => do writeVarInt 0x1a; Writer.bytes d
  | pathResponse d => do writeVarInt 0x1b; Writer.bytes d
  | connectionClose app e ft r => do
    writeVarInt (if app then 0x1d else 0x1c)
    writeVarInt e
    unless app do writeVarInt ft
    writeVarInt r.size
    Writer.bytes r
  | handshakeDone => writeVarInt 0x1e

/-- The bytes `write` produces, assuming every integer fits. -/
def encode (f : Frame) : ByteArray :=
  match Writer.run f.write with
  | .ok b => b
  | .error _ => ByteArray.empty

/-- The encoded size of a STREAM frame header for these fields (offset present when nonzero,
length always present). -/
def streamOverhead (id offset len : Nat) : Nat :=
  1 + varIntLen id + (if offset != 0 then varIntLen offset else 0) + varIntLen len

def cryptoOverhead (offset len : Nat) : Nat := 1 + varIntLen offset + varIntLen len

/-- The frames of an ACK frame's body, its type already read. -/
private def ackBody (ecn : Bool) : Parser Frame := do
  let largest ← varint
  let delay ← varint
  let count ← varint
  let first ← varint
  if first > largest then Parser.fail
  let mut lo := largest - first
  let mut ranges := [(lo, largest)]
  if count > (← Parser.remaining) then Parser.fail
  for _ in [0:count] do
    let gap ← varint
    let len ← varint
    if gap + 2 + len > lo then Parser.fail
    let hi := lo - gap - 2
    lo := hi - len
    ranges := (lo, hi) :: ranges
  if ecn then
    discard varint; discard varint; discard varint
  pure (.ack ranges.reverse delay)

def parse : Parser Frame := do
  let typ ← varint
  match typ with
  | 0x00 =>
    let mut n := 1
    for _ in [0:(← Parser.remaining)] do
      let c ← get
      if (← read).get! c.pos != 0 then break
      discard Parser.u8
      n := n + 1
    pure (.padding n)
  | 0x01 => pure .ping
  | 0x02 => ackBody false
  | 0x03 => ackBody true
  | 0x04 => pure (.resetStream (← varint) (← varint) (← varint))
  | 0x05 => pure (.stopSending (← varint) (← varint))
  | 0x06 => do
    let off ← varint
    let len ← varint
    pure (.crypto off (← Parser.bytes len))
  | 0x07 => do
    let len ← varint
    if len == 0 then Parser.fail
    pure (.newToken (← Parser.bytes len))
  | 0x10 => pure (.maxData (← varint))
  | 0x11 => pure (.maxStreamData (← varint) (← varint))
  | 0x12 => pure (.maxStreams true (← varint))
  | 0x13 => pure (.maxStreams false (← varint))
  | 0x14 => pure (.dataBlocked (← varint))
  | 0x15 => pure (.streamDataBlocked (← varint) (← varint))
  | 0x16 => pure (.streamsBlocked true (← varint))
  | 0x17 => pure (.streamsBlocked false (← varint))
  | 0x18 => do
    let s ← varint
    let r ← varint
    let len := (← Parser.u8).toNat
    if len == 0 || len > 20 || r > s then Parser.fail
    let cid ← Parser.bytes len
    pure (.newConnectionId s r cid (← Parser.bytes 16))
  | 0x19 => pure (.retireConnectionId (← varint))
  | 0x1a => pure (.pathChallenge (← Parser.bytes 8))
  | 0x1b => pure (.pathResponse (← Parser.bytes 8))
  | 0x1c => do
    let e ← varint
    let ft ← varint
    let len ← varint
    pure (.connectionClose false e ft (← Parser.bytes len))
  | 0x1d => do
    let e ← varint
    let len ← varint
    pure (.connectionClose true e 0 (← Parser.bytes len))
  | 0x1e => pure .handshakeDone
  | t =>
    if 0x08 ≤ t ∧ t ≤ 0x0f then do
      let id ← varint
      let off ← if t &&& 0x04 != 0 then varint else pure 0
      let len ← if t &&& 0x02 != 0 then varint else Parser.remaining
      if off + len > VarInt.max then Parser.fail
      pure (.stream id off (← Parser.bytes len) (t &&& 0x01 != 0))
    else Parser.fail

/-- The frames of a decrypted payload; an empty payload is a protocol violation. -/
def parseAll (payload : ByteArray) : Option (Array Frame) :=
  if payload.size == 0 then none else
  match Parser.run (Parser.many parse) payload with
  | .ok fs => some fs
  | .error _ => none

end Frame

end LeanQUIC
