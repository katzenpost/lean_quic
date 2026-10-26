/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import LeanQUIC.Connection
import Cryptlib.Primitives.MAC.HMAC

namespace LeanQUIC.Endpoint

open Cryptlib.Primitives.MAC.HMAC (hmacSha256)
open Cryptlib.Util.Bytes (ofVector)

/-! # A server endpoint's answer to a new client

What to do with an Initial whose Destination Connection ID belongs to no connection: as
katzenpost's QUIC servers do, first answer with a Retry (RFC 9000 §8.1.2), whose token binds the
client's address, its original Destination Connection ID and the time it was issued under the
endpoint's key, and accept the connection only when the client comes back with that token before
it expires. The token is the address proof: a server holds no state for a client until it has
one.

Times are the endpoint's own clock in microseconds (`UDP.nowUs` is monotonic and starts afresh
with each process), so a token can only be checked by the process that issued it; a `tokenKey`
drawn per process, as the examples do, makes sure of that. -/

structure Config where
  quic : LeanQUIC.Config := {}
  tls : LeanTLS.Handshake.Server.Config
  retry : Bool := true
  /-- The key retry tokens are authenticated under. -/
  tokenKey : ByteArray
  /-- How long a retry token stays valid, in microseconds. -/
  tokenLifetime : Nat := 10_000_000

/-- `n` as 8 big-endian bytes. -/
def be64 (n : Nat) : ByteArray :=
  ⟨(Array.range 8).map fun i => UInt8.ofNat (n >>> (8 * (7 - i)))⟩

def readBe64 (b : ByteArray) : Nat :=
  b.foldl (fun acc x => acc * 256 + x.toNat) 0

/-- `HMAC(key, address ‖ odcid ‖ issued ‖ the Retry's connection ID)`, truncated to 16 bytes. -/
def tokenTag (key addr odcid issued rcid : ByteArray) : ByteArray :=
  (ofVector (hmacSha256 key
    (addr ++ ⟨#[UInt8.ofNat odcid.size]⟩ ++ odcid ++ issued ++ rcid))).extract 0 16

/-- `len ‖ odcid ‖ issued (8 bytes) ‖ tag (16 bytes)`. -/
def makeToken (key addr odcid rcid : ByteArray) (now : Nat) : ByteArray :=
  let issued := be64 now
  ⟨#[UInt8.ofNat odcid.size]⟩ ++ odcid ++ issued ++ tokenTag key addr odcid issued rcid

/-- The original Destination Connection ID in a token, if the token is ours for this address and
this Retry connection ID, and was issued no more than `lifetime` before `now`. -/
def checkToken (key addr rcid token : ByteArray) (now lifetime : Nat) : Option ByteArray :=
  if token.size < 1 then none else
  let n := (token.get! 0).toNat
  if n < 8 || n > 20 || token.size != 1 + n + 8 + 16 then none else
  let odcid := token.extract 1 (1 + n)
  let issued := token.extract (1 + n) (1 + n + 8)
  let t := readBe64 issued
  if LeanTLS.Handshake.ctEq (token.extract (1 + n + 8) token.size)
      (tokenTag key addr odcid issued rcid) && t ≤ now && now - t ≤ lifetime then
    some odcid
  else none

/-- A stateless reset for a packet of `size` bytes to `dcid` (RFC 9000 §10.3): shorter than what
prompted it, at least 21 bytes, unpredictable bytes and then the reset token. -/
def statelessReset (key dcid filler : ByteArray) (size : Nat) : ByteArray :=
  let len := min (size - 1) 43
  ⟨#[0x40 ||| (filler.get! 0 &&& 0x3f)]⟩ ++ filler.extract 1 (len - 16) ++ resetToken key dcid

inductive Decision where
  | drop
  /-- Send this Retry packet back. -/
  | retry (packet : ByteArray)
  /-- Send this stateless reset back. -/
  | reset (packet : ByteArray)
  /-- A new connection, to be found by these connection IDs; it has not yet seen the datagram. -/
  | accept (conn : Conn) (cids : List ByteArray)

/-- The endpoint's decision for a datagram from `addr` with no connection. `fresh` is a new random
connection ID and `seed` the new connection's entropy. -/
def onUnknown (cfg : Config) (addr dgram : ByteArray) (now : Nat) (fresh : ByteArray)
    (seed : Vector UInt8 32) : Decision :=
  match parseHeader dgram 0 cidLength with
  | some (.long .initial 1 dcid scid token _, _) =>
    -- RFC 9000 §14.1: Initials in datagrams under 1200 bytes are dropped.
    if dgram.size < maxDatagram || dcid.size < 8 then .drop
    else if !cfg.retry then
      .accept (Conn.newServer cfg.quic cfg.tls seed fresh dcid scid now) [dcid, fresh]
    else if token.size == 0 then
      .retry (retryPacket dcid scid fresh (makeToken cfg.tokenKey addr dcid fresh now))
    else match checkToken cfg.tokenKey addr dcid token now cfg.tokenLifetime with
      | some odcid =>
        .accept (Conn.newServer cfg.quic cfg.tls seed dcid odcid scid now (some dcid)) [dcid]
      | none => .drop
  | some (.short dcid _, _) =>
    -- A packet for a connection we do not have: tell the peer, if it is long enough that the
    -- reset can be shorter and still look like a packet.
    if cfg.quic.resetKey.isEmpty || dgram.size ≤ 41 then .drop
    else .reset (statelessReset cfg.quic.resetKey dcid (Conn.deriveSecret seed "reset filler") dgram.size)
  | _ => .drop

end LeanQUIC.Endpoint
