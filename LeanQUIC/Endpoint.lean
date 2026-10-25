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
client's address and its original Destination Connection ID under the endpoint's key, and accept
the connection only when the client comes back with that token. The token is the address proof:
a server holds no state for a client until it has one. -/

structure Config where
  quic : LeanQUIC.Config := {}
  tls : LeanTLS.Handshake.Server.Config
  retry : Bool := true
  /-- The key retry tokens are authenticated under. -/
  tokenKey : ByteArray

/-- `HMAC(key, address ‖ odcid ‖ the Retry's connection ID)`, truncated to 16 bytes. -/
def tokenTag (key addr odcid rcid : ByteArray) : ByteArray :=
  (ofVector (hmacSha256 key (addr ++ ⟨#[UInt8.ofNat odcid.size]⟩ ++ odcid ++ rcid))).extract 0 16

def makeToken (key addr odcid rcid : ByteArray) : ByteArray :=
  ⟨#[UInt8.ofNat odcid.size]⟩ ++ odcid ++ tokenTag key addr odcid rcid

/-- The original Destination Connection ID in a token, if the token is ours for this address and
this Retry connection ID. -/
def checkToken (key addr rcid token : ByteArray) : Option ByteArray :=
  if token.size < 1 then none else
  let n := (token.get! 0).toNat
  if n < 8 || n > 20 || token.size != 1 + n + 16 then none else
  let odcid := token.extract 1 (1 + n)
  if LeanTLS.Handshake.ctEq (token.extract (1 + n) token.size) (tokenTag key addr odcid rcid) then
    some odcid
  else none

inductive Decision where
  | drop
  /-- Send this Retry packet back. -/
  | retry (packet : ByteArray)
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
      .retry (retryPacket dcid scid fresh (makeToken cfg.tokenKey addr dcid fresh))
    else match checkToken cfg.tokenKey addr dcid token with
      | some odcid =>
        .accept (Conn.newServer cfg.quic cfg.tls seed dcid odcid scid now (some dcid)) [dcid]
      | none => .drop
  | _ => .drop

end LeanQUIC.Endpoint
