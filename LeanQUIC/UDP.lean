/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Std.Async.UDP
import Std.Async.Timer
import Std.Time
import Std.Data.HashMap
import LeanQUIC.Connection
import LeanQUIC.Endpoint
import LeanTLS.X509

namespace LeanQUIC.UDP

open Std.Async
open Std.Async.UDP (Socket)
open Std.Net
open Cryptlib.Util.Bytes (ofVector toVecN)

/-! # Running connections over UDP

The only IO in lean_quic: a socket from Lean's `Std.Async.UDP`, the clock, and the system's
randomness. Each loop sends what the connection has to send, then waits for a datagram or the
connection's next deadline, whichever comes first. -/

def nowUs : IO Nat := do pure ((← IO.monoNanosNow) / 1000)

def randomBytes (n : Nat) : IO ByteArray := IO.getRandomBytes n.toUSize

def randomSeed : IO (Vector UInt8 32) := do pure (toVecN 32 (← randomBytes 32))

/-- `a.b.c.d:port`. -/
def parseAddr (s : String) : Option SocketAddress := do
  let [host, port] := s.splitOn ":" | none
  let [a, b, c, d] := (host.splitOn ".").map String.toNat? | none
  let (some a, some b, some c, some d) := (a, b, c, d) | none
  let p ← port.toNat?
  if a > 255 || b > 255 || c > 255 || d > 255 || p > 65535 then none
  some (.v4 { addr := IPv4Addr.ofParts a.toUInt8 b.toUInt8 c.toUInt8 d.toUInt8, port := p.toUInt16 })

/-- With `LEANQUIC_DEBUG` set, a line on stderr per datagram and timeout. -/
def debug (msg : Unit → String) : IO Unit := do
  if (← IO.getEnv "LEANQUIC_DEBUG").isSome then IO.eprintln s!"[{(← nowUs) / 1000}] {msg ()}"

def sendAll (sock : Socket) (c : Conn) (addr : Option SocketAddress) : Async Conn := do
  let mut c := c
  for _ in [0:4096] do
    let (c', d) := c.poll (← nowUs)
    c := c'
    match d with
    | some d =>
      (debug fun _ => s!"send {d.size} bytes, first byte {d.get! 0}" : IO _)
      sock.send d addr
    | none => break
  pure c

inductive Event where
  | datagram (data : ByteArray) (from_ : Option SocketAddress)
  | timeout

/-- Wait for a datagram, or until `deadline` (µs). -/
def waitEvent (sock : Socket) (deadline : Option Nat) : Async Event := do
  let now ← nowUs
  let ms := match deadline with
    | some d => if d ≤ now then 0 else (d - now + 999) / 1000
    | none => 1000
  if ms == 0 then return .timeout
  (debug fun _ => s!"wait {ms} ms" : IO _)
  let sleep ← Sleep.mk (Std.Time.Millisecond.Offset.ofNat ms)
  let ev ← Selectable.one #[
    .case (sock.recvSelector 65536) fun (d, a) => do
      (debug fun _ => s!"recv {d.size} bytes from {repr (a.map toString)}" : IO _)
      pure (Event.datagram d a),
    .case sleep.selector fun _ => pure Event.timeout]
  sleep.stop
  pure ev

/-! ## Certificates in katzenpost's shape -/

/-- katzenpost's epochs: 20 minutes from 2017-06-01T00:00Z. -/
def epochGenesis : Nat := 1496275200
def epochPeriod : Nat := 1200

/-- A self-signed Ed25519 certificate valid from the start of the previous epoch to the start of
the epoch after next, as katzenpost's `epochCertificate`. -/
def epochCertificate (signingKey : Vector UInt8 32) : IO ByteArray := do
  let unix := (← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val.toNat
  let epoch := (unix - epochGenesis) / epochPeriod
  let serial ← randomBytes 16
  let key := ofVector (LeanTLS.Handshake.ed25519.pub signingKey)
  pure (LeanTLS.X509.selfSigned (fun m => ofVector (LeanTLS.Handshake.ed25519.sign signingKey m ()).1)
    key serial (epochGenesis + (epoch - 1) * epochPeriod) (epochGenesis + (epoch + 2) * epochPeriod))

def spkiPin (cert : ByteArray) : Option ByteArray :=
  match LeanTLS.X509.parseLeaf cert with
  | .ok leaf => some (LeanTLS.KeySchedule.hash leaf.spki)
  | .error _ => none

/-! ## Client -/

/-- Connect, then run `app` after every event until it returns a result or the connection
closes. -/
partial def runClient {α : Type} (cfg : Config) (tls : LeanTLS.Handshake.Client.Config)
    (server : SocketAddress) (app : Conn → IO (Conn × Option α)) : IO (Except String α) := do
  let sock ← Socket.mk
  sock.bind (.v4 { addr := IPv4Addr.ofParts 0 0 0 0, port := 0 })
  sock.connect server
  let conn ← match Conn.newClient cfg tls (← randomSeed) (← randomBytes cidLength) (← randomBytes cidLength)
      (← nowUs) with
    | .ok c => pure c
    | .error a => return .error s!"TLS: {repr a}"
  let rec loop (c : Conn) : Async (Except String α) := do
    let (c, r) ← (app c : IO _)
    if let some r := r then
      let c := c.close (← nowUs)
      discard <| sendAll sock c none
      return .ok r
    if c.isClosed then
      return .error s!"connection closed: {repr c.closeReason}"
    let c ← sendAll sock c none
    let c ← match ← waitEvent sock c.nextTimeout with
      | .datagram d _ => pure (c.recv (← nowUs) d)
      | .timeout => pure (c.onTimeout (← nowUs))
    loop c
  (loop conn).block

/-! ## Server -/

structure Peer where
  addr : SocketAddress
  conn : Conn
  /-- The addresses the peer was last seen at, by the name the connection knows them by. -/
  addrs : List (ByteArray × SocketAddress) := []
  /-- The connection IDs the endpoint gave the connection at first. -/
  initial : List ByteArray
  /-- The connection IDs that lead to it now. -/
  cids : List ByteArray

structure Peers where
  conns : Std.HashMap Nat Peer := {}
  /-- Every connection ID a connection uses, and the client's original Destination Connection ID,
  lead to it. -/
  byCid : Std.HashMap ByteArray Nat := {}
  next : Nat := 0

/-- Store connection `i`, routing its connection IDs as they stand now. -/
def Peers.put (ps : Peers) (i : Nat) (p : Peer) : Peers :=
  let want := (p.initial ++ p.conn.activeLocalCids).eraseDups
  let byCid := p.cids.foldl (fun m c => if want.contains c then m else m.erase c) ps.byCid
  { ps with conns := ps.conns.insert i { p with cids := want },
            byCid := want.foldl (fun m c => m.insert c i) byCid }

/-- Serve forever: connections are found by the Destination Connection ID of each datagram, and
`app` is run on a connection after each of its events. -/
partial def runServer (cfg : Endpoint.Config) (listen : SocketAddress)
    (app : Conn → Conn) (onReady : IO Unit) : IO Unit := do
  -- One reset key for every connection, so the endpoint can reset ones it has lost.
  let resetKey ← if cfg.quic.resetKey.isEmpty then randomBytes 32 else pure cfg.quic.resetKey
  let cfg := { cfg with quic := { cfg.quic with resetKey } }
  let sock ← Socket.mk
  sock.bind listen
  onReady
  let rec loop (ps : Peers) : Async Unit := do
    let mut ps := ps
    -- Send, and drop closed connections.
    for (i, p) in ps.conns.toList do
      if p.conn.isClosed then
        ps := { ps with conns := ps.conns.erase i, byCid := p.cids.foldl (·.erase ·) ps.byCid }
      else
        -- Send where the connection says the peer is; it moves only to a validated new path.
        let addr := (p.addrs.find? (·.1 == p.conn.peerAddr)).map (·.2) |>.getD p.addr
        let c ← sendAll sock p.conn (some addr)
        ps := ps.put i { p with conn := c }
    let deadline := ps.conns.fold (fun acc _ p => match acc, p.conn.nextTimeout with
      | some a, some b => some (min a b) | none, b => b | a, none => a) none
    match ← waitEvent sock deadline with
    | .timeout =>
      let now ← nowUs
      for (i, p) in ps.conns.toList do
        if p.conn.nextTimeout.any (· ≤ now) then
          ps := ps.put i { p with conn := app (p.conn.onTimeout now) }
    | .datagram d (some addr) =>
      let now ← nowUs
      match parseHeader d 0 cidLength with
      | some (hdr, _) =>
        let dcid := hdr.dcid
        match ps.byCid[dcid]?.bind (ps.conns[·]?) with
        | some p =>
          let i := ps.byCid[dcid]!
          let name := (toString addr).toUTF8
          let addrs := ((name, addr) :: p.addrs.filter (·.1 != name)).take 4
          ps := ps.put i { p with addrs, conn := app (p.conn.recvFrom now name d) }
        | none =>
          let fresh ← (randomBytes cidLength : IO _)
          let seed ← (randomSeed : IO _)
          match Endpoint.onUnknown cfg (toString addr).toUTF8 d now fresh seed with
          | .drop => pure ()
          | .retry pkt => sock.send pkt (some addr)
          | .reset pkt => sock.send pkt (some addr)
          | .accept c cids =>
            let name := (toString addr).toUTF8
            let c := app (c.recvFrom now name d)
            let i := ps.next
            ps := { ps with next := i + 1 }.put i
              { addr, addrs := [(name, addr)], conn := c, initial := cids, cids := [] }
      | none => pure ()
    | .datagram _ none => pure ()
    loop ps
  (loop {}).block

/-- The server application of the interop tests: every stream echoed back, finished when the
client finishes. -/
def echo (c : Conn) : Conn := Id.run do
  let (c, _) := c.takeIncoming
  let mut c := c
  for (id, _) in c.streams.toList do
    let (c', data) := c.read id (c.readable id)
    c := c'.write id data
    if c.recvFinished id then c := c.finish id
    c := c.retire id
  pure c

end LeanQUIC.UDP
