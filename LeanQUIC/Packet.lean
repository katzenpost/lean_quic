/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import LeanQUIC.VarInt
import LeanTLS.CipherSuite
import LeanTLS.KeySchedule
import Cryptlib.Util.Bytes

namespace LeanQUIC

open LeanTLS (Suite CipherSuite)
open LeanTLS.KeySchedule (hkdfExtract expandLabel quicKeys)
open LeanTLS.Wire
open Cryptlib.Util.Bytes (ofVector toVecN)

/-! # QUIC version 1 packets and their protection (RFC 9000 §17, RFC 9001 §5)

A packet's payload is sealed by the AEAD of its encryption level, with the header as associated
data and a nonce built from the packet number; then header protection masks the packet number and
the low bits of the first byte with a function of a sample of the ciphertext.

The laws: `openPayload_sealPayload`, that the AEAD's own correctness carries over to packets, and
`applyMask_applyMask`, that header protection undoes itself. -/

def version1 : Nat := 1

/-- RFC 9001 §5.2. -/
def initialSalt : ByteArray := ⟨#[0x38, 0x76, 0x2c, 0xf7, 0xf5, 0x59, 0x34, 0xb3, 0x4d, 0x17,
  0x9a, 0xe6, 0xa4, 0xc8, 0x0c, 0xad, 0xcc, 0xbb, 0x7f, 0x0a]⟩

/-- The keys protecting one direction of one encryption level. -/
structure Keys where
  suite  : Suite
  key    : suite.cipherSuite.aead.Key
  iv     : ByteArray
  hp     : ByteArray
  secret : ByteArray

def Keys.ofSecret (suite : Suite) (secret : ByteArray) : Keys :=
  let cs := suite.cipherSuite
  let pk := quicKeys secret cs.aead.keySize
  { suite, key := cs.key pk.key, iv := pk.iv, hp := pk.hp, secret }

/-- The client's and the server's Initial secrets, from the client's first Destination
Connection ID. -/
def initialSecrets (dcid : ByteArray) : ByteArray × ByteArray :=
  let s := hkdfExtract initialSalt dcid
  (expandLabel s "client in" ByteArray.empty 32, expandLabel s "server in" ByteArray.empty 32)

def initialKeys (dcid : ByteArray) : Keys × Keys :=
  let (c, s) := initialSecrets dcid
  (Keys.ofSecret .aes128gcm c, Keys.ofSecret .aes128gcm s)

/-- The next generation of 1-RTT keys; the header protection key is kept (RFC 9001 §6). -/
def Keys.next (k : Keys) : Keys :=
  { Keys.ofSecret k.suite (LeanTLS.KeySchedule.quicNextSecret k.secret) with hp := k.hp }

/-- The IV with the packet number, left-padded to 12 bytes, XORed in (RFC 9001 §5.3). -/
def nonce (iv : ByteArray) (pn : Nat) : Vector UInt8 12 :=
  Vector.ofFn fun i => iv.get! i.val ^^^ UInt8.ofNat (pn >>> (8 * (11 - i.val)))

def sealPayload (k : Keys) (pn : Nat) (header payload : ByteArray) : ByteArray :=
  k.suite.cipherSuite.aead.encrypt k.key (k.suite.cipherSuite.nonce (nonce k.iv pn)) header payload

def openPayload (k : Keys) (pn : Nat) (header ct : ByteArray) : Option ByteArray :=
  k.suite.cipherSuite.aead.decrypt k.key (k.suite.cipherSuite.nonce (nonce k.iv pn)) header ct

theorem openPayload_sealPayload (k : Keys) (pn : Nat) (header payload : ByteArray) :
    openPayload k pn header (sealPayload k pn header payload) = some payload :=
  k.suite.cipherSuite.aead.decrypt_encrypt _ _ _ _

theorem size_sealPayload (k : Keys) (pn : Nat) (header payload : ByteArray) :
    (sealPayload k pn header payload).size = payload.size + k.suite.cipherSuite.aead.tagSize :=
  k.suite.cipherSuite.aead.size_encrypt _ _ _ _

def tagSize : Nat := 16

/-! ## Header protection -/

def mask (k : Keys) (sample : Vector UInt8 16) : Vector UInt8 5 :=
  k.suite.cipherSuite.hpMask k.hp sample

/-- XOR the mask into the first byte (its low 4 bits for a long header, 5 for a short one) and the
`pnLen` packet number bytes at `pnOffset`. -/
def applyMask (long : Bool) (pkt : ByteArray) (pnOffset pnLen : Nat) (m : Vector UInt8 5) :
    ByteArray :=
  let bits : UInt8 := if long then 0x0f else 0x1f
  ⟨pkt.data.mapIdx fun i b =>
    if i = 0 then b ^^^ (m[0] &&& bits)
    else if pnOffset ≤ i ∧ i < pnOffset + pnLen ∧ i - pnOffset < 4 then
      b ^^^ m.toArray.getD (i - pnOffset + 1) 0
    else b⟩

theorem applyMask_applyMask (long : Bool) (pkt : ByteArray) (pnOffset pnLen : Nat)
    (m : Vector UInt8 5) :
    applyMask long (applyMask long pkt pnOffset pnLen m) pnOffset pnLen m = pkt := by
  apply ByteArray.ext
  apply Array.ext
  · simp [applyMask]
  · intro i h1 h2
    simp only [applyMask, Array.getElem_mapIdx]
    split
    · rw [UInt8.xor_assoc, UInt8.xor_self, UInt8.xor_zero]
    · rename_i hc0
      by_cases hc : pnOffset ≤ i ∧ i < pnOffset + pnLen ∧ i - pnOffset < 4
      · simp only [hc, and_self, if_true, UInt8.xor_assoc, UInt8.xor_self, UInt8.xor_zero]
      · simp only [hc, if_false]

def sampleAt (pkt : ByteArray) (pos : Nat) : Vector UInt8 16 := toVecN 16 (pkt.extract pos (pos + 16))

/-! ## Packet numbers (RFC 9000 §17.1, Appendix A) -/

/-- Bytes to encode `pn` so that a peer that has acknowledged `largestAcked` decodes it. -/
def pnLength (pn : Nat) (largestAcked : Option Nat) : Nat :=
  let unacked := match largestAcked with | some a => pn - a | none => pn + 1
  if unacked < 2 ^ 7 then 1 else if unacked < 2 ^ 15 then 2 else if unacked < 2 ^ 23 then 3 else 4

def encodePn (pn len : Nat) : ByteArray :=
  ⟨Array.ofFn fun i : Fin len => UInt8.ofNat (pn >>> (8 * (len - 1 - i.val)))⟩

/-- The full packet number closest to the next expected one with these low `len` bytes. -/
def decodePn (largest : Option Nat) (truncated len : Nat) : Nat :=
  let expected := match largest with | some l => l + 1 | none => 0
  let win := 2 ^ (8 * len)
  let hwin := win / 2
  let candidate := expected / win * win + truncated
  if candidate + hwin ≤ expected ∧ candidate + win < 2 ^ 62 then candidate + win
  else if candidate > expected + hwin ∧ candidate ≥ win then candidate - win
  else candidate

/-! ## Headers -/

inductive LongType where
  | initial
  | zeroRtt
  | handshake
  | retry
deriving DecidableEq, Repr, Inhabited

def LongType.bits : LongType → UInt8
  | initial => 0
  | zeroRtt => 1
  | handshake => 2
  | retry => 3

/-- A packet's header fields as parsed before header protection is removed. Offsets are from the
start of the packet. -/
inductive Header where
  | long (typ : LongType) (version : Nat) (dcid scid token : ByteArray) (pnOffset : Nat)
  | short (dcid : ByteArray) (pnOffset : Nat)
  | versionNegotiation (dcid scid : ByteArray)

def Header.dcid : Header → ByteArray
  | .long _ _ d _ _ _ => d
  | .short d _ => d
  | .versionNegotiation d _ => d

/-- The packet at `pos` in a datagram: its header and the end of the packet, which for coalesced
long packets is given by their Length field. Short header packets use `shortDcidLen`. -/
def parseHeader (dgram : ByteArray) (pos : Nat) (shortDcidLen : Nat) : Option (Header × Nat) :=
  let pkt := dgram.extract pos dgram.size
  let p : Parser (Header × Nat) := do
    let b0 ← Parser.u8
    if b0 &&& 0x80 == 0 then
      let dcid ← Parser.bytes shortDcidLen
      pure (.short dcid (1 + shortDcidLen), pkt.size)
    else
      let version ← Parser.u32
      let dcid ← Parser.opaque8
      let scid ← Parser.opaque8
      if dcid.size > 20 || scid.size > 20 then Parser.fail
      if version == 0 then
        discard <| Parser.bytes (← Parser.remaining)
        return (.versionNegotiation dcid scid, pkt.size)
      if b0 &&& 0x40 == 0 then Parser.fail
      let typ : LongType := match (b0 >>> 4) &&& 3 with
        | 0 => .initial | 1 => .zeroRtt | 2 => .handshake | _ => .retry
      if typ == .retry then
        let rest ← Parser.bytes (← Parser.remaining)
        if rest.size < tagSize then Parser.fail
        return (.long .retry version dcid scid (rest.extract 0 (rest.size - tagSize)) 0, pkt.size)
      let token ← if typ == .initial then do Parser.bytes (← varint) else pure ByteArray.empty
      let len ← varint
      let pnOffset := (← get).pos
      if pnOffset + len > pkt.size then Parser.fail
      discard <| Parser.bytes (← Parser.remaining)
      pure (.long typ version dcid scid token pnOffset, pnOffset + len)
  match (p pkt).run ⟨0, pkt.size⟩ with
  | .ok (r, _) => some r
  | .error _ => none

/-- A long header through the packet number, with a 2-byte Length for `pnLen + payloadLen`
bytes plus the tag. -/
def longHeader (typ : LongType) (dcid scid token : ByteArray) (pn pnLen payloadLen : Nat) :
    ByteArray :=
  let b0 : UInt8 := (0xc0 : UInt8) ||| (typ.bits <<< 4) ||| UInt8.ofNat (pnLen - 1)
  let tokenPart := if typ == .initial then encodeVarInt token.size ++ token else ByteArray.empty
  ⟨#[b0, 0, 0, 0, 1, UInt8.ofNat dcid.size]⟩ ++ dcid ++ ⟨#[UInt8.ofNat scid.size]⟩ ++ scid ++
    tokenPart ++ encodeVarIntLen 2 (pnLen + payloadLen + tagSize) ++ encodePn pn pnLen

def shortHeader (dcid : ByteArray) (keyPhase : Bool) (pn pnLen : Nat) : ByteArray :=
  let b0 : UInt8 := (0x40 : UInt8) ||| (if keyPhase then 0x04 else 0) ||| UInt8.ofNat (pnLen - 1)
  ⟨#[b0]⟩ ++ dcid ++ encodePn pn pnLen

/-- Protect a packet: `header` ends with the `pnLen` packet number bytes. The payload must make
`pnLen + payload + tag` at least 20 bytes, so that there is a sample. -/
def protect (k : Keys) (long : Bool) (header : ByteArray) (pn pnLen : Nat) (payload : ByteArray) :
    ByteArray :=
  let pnOffset := header.size - pnLen
  let pkt := header ++ sealPayload k pn header payload
  applyMask long pkt pnOffset pnLen (mask k (sampleAt pkt (pnOffset + 4)))

structure Opened where
  pn : Nat
  /-- The first byte with header protection removed. -/
  firstByte : UInt8
  payload : ByteArray

/-- Remove header protection and open one packet (`pkt` is exactly the packet). `largest` is the
largest packet number received in the space. -/
def openPacket (k : Keys) (long : Bool) (pkt : ByteArray) (pnOffset : Nat) (largest : Option Nat) :
    Option Opened := do
  if pnOffset + 4 + 16 > pkt.size then none
  let m := mask k (sampleAt pkt (pnOffset + 4))
  let b0 := pkt.get! 0 ^^^ (m[0] &&& (if long then 0x0f else 0x1f))
  let pnLen := (b0 &&& 3).toNat + 1
  let plain := applyMask long pkt pnOffset pnLen m
  let truncated := (plain.extract pnOffset (pnOffset + pnLen)).foldl (fun a x => a * 256 + x.toNat) 0
  let pn := decodePn largest truncated pnLen
  let header := plain.extract 0 (pnOffset + pnLen)
  let payload ← openPayload k pn header (plain.extract (pnOffset + pnLen) plain.size)
  pure { pn, firstByte := b0, payload }

/-! ## Retry (RFC 9001 §5.8) -/

def retryKey : ByteArray := ⟨#[0xbe, 0x0c, 0x69, 0x0b, 0x9f, 0x66, 0x57, 0x5a, 0x1d, 0x76, 0x6b,
  0x54, 0xe3, 0x68, 0xc8, 0x4e]⟩
def retryNonce : Vector UInt8 12 := #v[0x46, 0x15, 0x99, 0xd3, 0x5d, 0x63, 0x2b, 0xf2, 0x23, 0x98,
  0x25, 0xbb]

/-- The integrity tag over the Retry packet without its tag, bound to the client's original
Destination Connection ID. -/
def retryTag (odcid retryWithoutTag : ByteArray) : ByteArray :=
  let cs := LeanTLS.aes128gcm
  cs.aead.encrypt (cs.key retryKey) (cs.nonce retryNonce)
    (⟨#[UInt8.ofNat odcid.size]⟩ ++ odcid ++ retryWithoutTag) ByteArray.empty

def retryPacket (odcid dcid scid token : ByteArray) : ByteArray :=
  let body := ⟨#[0xff, 0, 0, 0, 1, UInt8.ofNat dcid.size]⟩ ++ dcid ++ ⟨#[UInt8.ofNat scid.size]⟩ ++
    scid ++ token
  body ++ retryTag odcid body

def retryValid (odcid pkt : ByteArray) : Bool :=
  pkt.size ≥ tagSize &&
    retryTag odcid (pkt.extract 0 (pkt.size - tagSize)) == pkt.extract (pkt.size - tagSize) pkt.size

end LeanQUIC
