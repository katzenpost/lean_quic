/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import LeanQUIC.VarInt

namespace LeanQUIC

open LeanTLS.Wire

/-! # Transport parameters (RFC 9000 §18)

Carried in the TLS `quic_transport_parameters` extension. Unknown parameters are ignored; a
parameter given twice is an error. -/

structure TransportParams where
  originalDestinationConnectionId : Option ByteArray := none
  maxIdleTimeout : Nat := 0
  statelessResetToken : Option ByteArray := none
  maxUdpPayloadSize : Nat := 65527
  initialMaxData : Nat := 0
  initialMaxStreamDataBidiLocal : Nat := 0
  initialMaxStreamDataBidiRemote : Nat := 0
  initialMaxStreamDataUni : Nat := 0
  initialMaxStreamsBidi : Nat := 0
  initialMaxStreamsUni : Nat := 0
  ackDelayExponent : Nat := 3
  maxAckDelay : Nat := 25
  disableActiveMigration : Bool := false
  activeConnectionIdLimit : Nat := 2
  initialSourceConnectionId : Option ByteArray := none
  retrySourceConnectionId : Option ByteArray := none
deriving Inhabited

namespace TransportParams

private def int (id v : Nat) : Writer Unit := do
  writeVarInt id
  writeVarInt (varIntLen v)
  writeVarInt v

private def bytesParam (id : Nat) (b : ByteArray) : Writer Unit := do
  writeVarInt id
  writeVarInt b.size
  Writer.bytes b

def encode (p : TransportParams) : ByteArray :=
  let w : Writer Unit := do
    if let some c := p.originalDestinationConnectionId then bytesParam 0x00 c
    if p.maxIdleTimeout != 0 then int 0x01 p.maxIdleTimeout
    if let some t := p.statelessResetToken then bytesParam 0x02 t
    if p.maxUdpPayloadSize != 65527 then int 0x03 p.maxUdpPayloadSize
    int 0x04 p.initialMaxData
    int 0x05 p.initialMaxStreamDataBidiLocal
    int 0x06 p.initialMaxStreamDataBidiRemote
    int 0x07 p.initialMaxStreamDataUni
    int 0x08 p.initialMaxStreamsBidi
    int 0x09 p.initialMaxStreamsUni
    if p.ackDelayExponent != 3 then int 0x0a p.ackDelayExponent
    if p.maxAckDelay != 25 then int 0x0b p.maxAckDelay
    if p.disableActiveMigration then do writeVarInt 0x0c; writeVarInt 0
    if p.activeConnectionIdLimit != 2 then int 0x0e p.activeConnectionIdLimit
    if let some c := p.initialSourceConnectionId then bytesParam 0x0f c
    if let some c := p.retrySourceConnectionId then bytesParam 0x10 c
  match Writer.run w with
  | .ok b => b
  | .error _ => ByteArray.empty

private def intOf (b : ByteArray) : Option Nat :=
  match Parser.run varint b with
  | .ok v => some v
  | .error _ => none

def decode (b : ByteArray) : Option TransportParams := do
  let entries ← match Parser.run (Parser.many do
      let id ← varint
      let len ← varint
      pure (id, ← Parser.bytes len)) b with
    | .ok es => some es
    | .error _ => none
  let mut seen : Array Nat := #[]
  let mut p : TransportParams := {}
  for (id, v) in entries do
    if seen.contains id then none
    seen := seen.push id
    match id with
    | 0x00 => p := { p with originalDestinationConnectionId := some v }
    | 0x01 => p := { p with maxIdleTimeout := ← intOf v }
    | 0x02 =>
      if v.size != 16 then none
      p := { p with statelessResetToken := some v }
    | 0x03 =>
      let n ← intOf v
      if n < 1200 then none
      p := { p with maxUdpPayloadSize := n }
    | 0x04 => p := { p with initialMaxData := ← intOf v }
    | 0x05 => p := { p with initialMaxStreamDataBidiLocal := ← intOf v }
    | 0x06 => p := { p with initialMaxStreamDataBidiRemote := ← intOf v }
    | 0x07 => p := { p with initialMaxStreamDataUni := ← intOf v }
    | 0x08 => p := { p with initialMaxStreamsBidi := ← intOf v }
    | 0x09 => p := { p with initialMaxStreamsUni := ← intOf v }
    | 0x0a =>
      let n ← intOf v
      if n > 20 then none
      p := { p with ackDelayExponent := n }
    | 0x0b =>
      let n ← intOf v
      if n ≥ 2 ^ 14 then none
      p := { p with maxAckDelay := n }
    | 0x0c => p := { p with disableActiveMigration := true }
    | 0x0e =>
      let n ← intOf v
      if n < 2 then none
      p := { p with activeConnectionIdLimit := n }
    | 0x0f => p := { p with initialSourceConnectionId := some v }
    | 0x10 => p := { p with retrySourceConnectionId := some v }
    | _ => pure ()
  pure p

end TransportParams

end LeanQUIC
