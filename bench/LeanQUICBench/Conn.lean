/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import LeanQUIC
import LeanBench
import LeanQUICBench.Packet

/-! # A connection's per-packet work, and whole transfers, in process

A client and a server handshake by function calls, as in `example_sansio`. On the established
pair: `poll` making one 1-RTT packet of stream data, the server's `recv` of it, the client's `recv`
of an ACK for several packets, and transfers of a stream from client to server, with no sockets,
to compare per-packet totals with the single operations. Every connection is read from a ref, so
the timed action also pays for copying the shared parts it updates (the `Conn` structure and the
maps it inserts into), which a uniquely held connection would update in place. -/

namespace LeanQUICBench.Conn

open LeanQUIC
open LeanQUICBench.Packet (bytes suiteName)
open Cryptlib.Util.Bytes (ofVector)

def cfg : LeanBench.BenchConfig := { suite := some "quic", samples := 30, warmup := 3 }
def transferCfg : LeanBench.BenchConfig := { suite := some "quic", samples := 5, warmup := 1 }

def identity : Vector UInt8 32 := Vector.replicate 32 1
def cert : ByteArray :=
  LeanTLS.X509.selfSigned (fun m => ofVector (Cryptlib.Primitives.Sign.Ed25519Math.signNative identity m))
    (ofVector (LeanTLS.Handshake.ed25519.pub identity)) (ByteArray.mk (Array.replicate 16 1)) 0 86400
def pin : ByteArray := match LeanTLS.X509.parseLeaf cert with
  | .ok leaf => LeanTLS.KeySchedule.hash leaf.spki
  | .error _ => .empty

/-- Every datagram a connection has to send now. -/
def drain (c : Conn) (now : Nat) : Conn × Array ByteArray := Id.run do
  let mut c := c
  let mut out := #[]
  for _ in [0:1000] do
    let (c', d) := c.poll now
    c := c'
    match d with
    | some d => out := out.push d
    | none => break
  (c, out)

/-- One round: the client's datagrams to the server, then the server's to the client. -/
def exchange (now : Nat) (c s : Conn) : Conn × Conn × Nat := Id.run do
  let (c, ds) := drain c now
  let s := ds.foldl (fun s d => s.recv now d) s
  let (s, ds2) := drain s now
  let c := ds2.foldl (fun c d => c.recv now d) c
  (c, s, ds.size + ds2.size)

/-- An established client and server with nothing in flight, and the time. -/
def connect (suite : LeanTLS.Suite) : IO (Conn × Conn × Nat) := do
  let ctls : LeanTLS.Handshake.Client.Config :=
    { alpn := "h3".toUTF8, transportParams := .empty, pins := [pin], suites := [suite] }
  let stls : LeanTLS.Handshake.Server.Config :=
    { alpn := "h3".toUTF8, transportParams := .empty, signingKey := identity, certificate := cert }
  let cid (b : UInt8) : ByteArray := ByteArray.mk (Array.replicate 8 b)
  let .ok c := Conn.newClient {} ctls (Vector.replicate 32 2) (cid 1) (cid 2) 0
    | throw (IO.userError "TLS refused the configuration")
  let mut s := Conn.newServer {} stls (Vector.replicate 32 3) (cid 3) (cid 2) (cid 1) 0
  let mut c := c
  let mut now := 0
  for _ in [0:50] do
    now := now + 1000
    let (c', s', n) := exchange now c s
    c := c'
    s := s'
    if c.isEstablished && s.isEstablished && n == 0 then break
  -- Past every delayed acknowledgment, and quiet again.
  now := now + 30000
  c := c.onTimeout now
  s := s.onTimeout now
  for _ in [0:4] do
    now := now + 1000
    let (c', s', _) := exchange now c s
    c := c'
    s := s'
  unless c.isEstablished && s.isEstablished do throw (IO.userError "no connection")
  pure (c, s, now)

/-- Send `data` on a new client stream until the server has read all of it; the bytes read and
the datagrams sent both ways. -/
def transfer (c s : Conn) (now : Nat) (data : ByteArray) : Nat × Nat := Id.run do
  let (c, some id) := c.openStream | (0, 0)
  let mut c := (c.write id data).finish id
  let mut s := s
  let mut now := now
  let mut got := 0
  let mut dgrams := 0
  for _ in [0:1000000] do
    let (c', ds) := drain c now
    c := c'
    for d in ds do s := s.recv now d
    let (s', bytes) := s.read id (s.readable id)
    s := s'
    got := got + bytes.size
    let (s', ds2) := drain s now
    s := s'
    for d in ds2 do c := c.recv now d
    dgrams := dgrams + ds.size + ds2.size
    if got ≥ data.size then break
    if ds.isEmpty && ds2.isEmpty then
      match [c.nextTimeout, s.nextTimeout].filterMap _root_.id |>.min? with
      | some t =>
        now := max (now + 1) t
        c := c.onTimeout now
        s := s.onTimeout now
      | none => break
    else now := now + 100
  (got, dgrams)

def benches : IO (Array LeanBench.Bench) := do
  let connOut ← IO.mkRef (none : Option Conn)
  let pollOut ← IO.mkRef (none : Option (Conn × Option ByteArray))
  let nums ← IO.mkRef (0, 0)
  let mut bs := #[]
  for suite in [LeanTLS.Suite.chacha20poly1305, .aes128gcm] do
    let name := suiteName suite
    let (c0, s0, t0) ← connect suite
    let now ← IO.mkRef t0
    let idle ← IO.mkRef c0
    if (c0.poll t0).2.isSome then throw (IO.userError "the settled client has something to send")
    let (c1, some id) := c0.openStream | throw (IO.userError "no stream")
    let client ← IO.mkRef (c1.write id (bytes 65536))
    let (c2, some d) := (← client.get).poll t0 | throw (IO.userError "nothing to send")
    let dgram ← IO.mkRef d
    let server ← IO.mkRef s0
    let s1 := s0.recv t0 d
    IO.eprintln s!"{name}: 1-RTT datagram {d.size}B carrying {s1.readable id}B of stream data"
    if s1.readable id == 0 then throw (IO.userError "the server took no stream data")
    bs := bs.push { name := s!"{name} poll: nothing to send", config := cfg,
                    action := do pollOut.set (some ((← idle.get).poll (← now.get))) }
    bs := bs.push { name := s!"{name} poll: one 1-RTT packet of stream data", config := cfg,
                    action := do pollOut.set (some ((← client.get).poll (← now.get))) }
    bs := bs.push { name := s!"{name} recv: one 1-RTT packet of stream data", config := cfg,
                    action := do connOut.set (some ((← server.get).recv (← now.get) (← dgram.get))) }
    -- The second of two calls works on a connection it holds alone.
    let (_, some d2) := c2.poll t0 | throw (IO.userError "nothing to send")
    let dgram2 ← IO.mkRef d2
    bs := bs.push { name := s!"{name} poll: two 1-RTT packets in a row", config := cfg,
                    action := do
                      let t ← now.get
                      let (c, _) := (← client.get).poll t
                      pollOut.set (some (c.poll t)) }
    bs := bs.push { name := s!"{name} recv: two 1-RTT packets in a row", config := cfg,
                    action := do
                      let t ← now.get
                      connOut.set (some (((← server.get).recv t (← dgram.get)).recv t (← dgram2.get))) }
    -- The two halves of `poll`: choosing the frames, and sealing them.
    let budget := maxDatagram - ((← client.get).headerOverhead .application + tagSize)
    let builtOut ← IO.mkRef (none : Option (Conn × Conn.Built))
    bs := bs.push { name := s!"{name} poll part: buildFrames", config := cfg,
                    action := do
                      builtOut.set (some ((← client.get).buildFrames (← now.get) .application budget true)) }
    let (cb, b) := (← client.get).buildFrames t0 .application budget true
    let built ← IO.mkRef (cb, b)
    let sealOut ← IO.mkRef (none : Option (Conn × ByteArray))
    bs := bs.push { name := s!"{name} poll part: sealPacket", config := cfg,
                    action := do
                      let (c, b) ← built.get
                      sealOut.set (some (c.sealPacket (← now.get) .application b 0)) }
    -- The half of `recv` after opening: the frames of the opened packet.
    let some rk := s0.app.readKeys | throw (IO.userError "no read keys")
    let some o := openPacket rk false d (1 + s0.localCid.size) s0.app.largestRecv
      | throw (IO.userError "the packet does not open")
    let opened ← IO.mkRef o
    bs := bs.push { name := s!"{name} recv part: onPacket", config := cfg,
                    action := do
                      let o ← opened.get
                      connOut.set (some ((← server.get).onPacket (← now.get) .application o.pn o.payload)) }
    -- The client sends `k` packets; the server's ACK for all of them, 20 ms later.
    for k in [2, 8] do
      let mut c := c2
      let mut s := s1
      for _ in [1:k] do
        let (c', some d) := c.poll t0 | throw (IO.userError "nothing to send")
        c := c'
        s := s.recv t0 d
      let (_, acks) := drain s (t0 + 20000)
      let some ack := acks[0]? | throw (IO.userError "no ACK")
      let after := c.recv (t0 + 20000) ack
      unless after.recovery.bytesInFlight == 0 do
        throw (IO.userError s!"{k} packets: {after.recovery.bytesInFlight} bytes still in flight")
      let sender ← IO.mkRef c
      let ackRef ← IO.mkRef ack
      let later ← IO.mkRef (t0 + 20000)
      bs := bs.push { name := s!"{name} recv: ACK of {k} packets", config := cfg,
                      action := do connOut.set (some ((← sender.get).recv (← later.get) (← ackRef.get))) }
    let pair ← IO.mkRef (c0, s0)
    for (size, label) in [(65536, "64KiB"), (262144, "256KiB"), (1048576, "1MiB")] do
      let data ← IO.mkRef (bytes size)
      let (got, n) := transfer c0 s0 t0 (← data.get)
      IO.eprintln s!"{name}: {label} transfer, {n} datagrams"
      unless got == size do throw (IO.userError s!"{label} transfer: {got} bytes arrived")
      bs := bs.push { name := s!"{name} transfer {label} client to server", config := transferCfg,
                      action := do
                        let (c, s) ← pair.get
                        nums.set (transfer c s (← now.get) (← data.get)) }
  pure bs

end LeanQUICBench.Conn
