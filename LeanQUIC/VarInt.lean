/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import LeanTLS.Wire

namespace LeanQUIC

open LeanTLS.Wire

/-! # Variable-length integers (RFC 9000 §16)

The top two bits of the first byte give the length, 1, 2, 4 or 8 bytes; the rest is the value,
big-endian. Encoding uses the shortest form; decoding accepts any. -/

def VarInt.max : Nat := 2 ^ 62 - 1

/-- The length of the shortest encoding of `v`. -/
def varIntLen (v : Nat) : Nat :=
  if v < 2 ^ 6 then 1 else if v < 2 ^ 14 then 2 else if v < 2 ^ 30 then 4 else 8

/-- The encoding of `v` in exactly `len` bytes (1, 2, 4 or 8), which must hold it. -/
def encodeVarIntLen (len v : Nat) : ByteArray :=
  let prefixBits := match len with | 1 => 0 | 2 => 1 | 4 => 2 | _ => 3
  let bytes : Array UInt8 := Array.ofFn fun i : Fin len => UInt8.ofNat (v >>> (8 * (len - 1 - i.val)))
  ⟨bytes.modify 0 (· ||| UInt8.ofNat (prefixBits <<< 6))⟩

def encodeVarInt (v : Nat) : ByteArray := encodeVarIntLen (varIntLen v) v

def varint : Parser Nat := do
  let b0 ← Parser.u8
  let len := 1 <<< (b0 >>> 6).toNat
  let rest ← Parser.bytes (len - 1)
  pure (rest.foldl (fun acc x => acc * 256 + x.toNat) (b0 &&& 0x3f).toNat)

def writeVarInt (v : Nat) : Writer Unit := do
  -- `v ≤ VarInt.max`, without building the 62-bit bound from its decimal digits on every call
  if v >>> 62 = 0 then Writer.bytes (encodeVarInt v) else throw .internalError

end LeanQUIC
