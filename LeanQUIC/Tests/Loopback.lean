import LeanQUIC
import LeanTLS

open LeanQUIC
open LeanTLS
open Cryptlib.Util.Bytes (ofVector toVecN)

/-! A client and a server connection run against each other through a simulated network, in
process and without IO: datagrams take 10 ms, and the network can drop, reorder and duplicate
them. The client sends payloads on streams one after another and the server echoes them, as the
interop harness does over UDP. -/

def identity : Vector UInt8 32 := Vector.ofFn fun i => UInt8.ofNat (50 + i.val)
def serverKey : ByteArray := ofVector (LeanTLS.Handshake.ed25519.pub identity)
def serverCert : ByteArray :=
  X509.selfSigned (fun m => ofVector (LeanTLS.Handshake.ed25519.sign identity m ()).1) serverKey
    ⟨Array.replicate 16 9⟩ 1761433200 1761436800
def serverPin : ByteArray :=
  match X509.parseLeaf serverCert with
  | .ok leaf => KeySchedule.hash leaf.spki
  | .error _ => ByteArray.empty

def h3 : ByteArray := "h3".toUTF8
def serverTls : LeanTLS.Handshake.Server.Config :=
  { alpn := h3, transportParams := ByteArray.empty, signingKey := identity, certificate := serverCert }
def clientTls : LeanTLS.Handshake.Client.Config :=
  { alpn := h3, transportParams := ByteArray.empty, pins := [serverPin] }

/-- A deterministic generator for the network's choices. -/
structure Lcg where
  s : Nat

def Lcg.next (g : Lcg) : Lcg × Nat :=
  let s := (g.s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
  ({ s }, s >>> 33)

structure Net where
  dropPct : Nat
  reorderPct : Nat
  dupPct : Nat

structure Sim where
  now : Nat
  rng : Lcg
  client : Conn
  server : Option Conn := none
  /-- In flight: arrival time, to the server?, bytes. -/
  wire : Array (Nat × Bool × ByteArray) := #[]
  sentDatagrams : Nat := 0
  dropped : Nat := 0
  retries : Nat := 0

def pattern (n : Nat) : ByteArray := ⟨Array.ofFn fun i : Fin n => UInt8.ofNat (i.val % 251)⟩

def transmit (net : Net) (sim : Sim) (toServer : Bool) (d : ByteArray) : Sim := Id.run do
  let (rng, a) := sim.rng.next
  let (rng, b) := rng.next
  let (rng, c) := rng.next
  let mut sim := { sim with rng, sentDatagrams := sim.sentDatagrams + 1 }
  if a % 100 < net.dropPct then return { sim with dropped := sim.dropped + 1 }
  let delay := if b % 100 < net.reorderPct then 10000 + (b % 15000) else 10000
  sim := { sim with wire := sim.wire.push (sim.now + delay, toServer, d) }
  if c % 100 < net.dupPct then sim := { sim with wire := sim.wire.push (sim.now + delay + 3000, toServer, d) }
  pure sim

/-- Send everything both sides have to send now. -/
def flush (net : Net) (sim : Sim) : Sim := Id.run do
  let mut sim := sim
  for _ in [0:10000] do
    let (c, d) := sim.client.poll sim.now
    sim := { sim with client := c }
    match d with
    | some d => sim := transmit net sim true d
    | none => break
  if let some srv := sim.server then
    let mut srv := srv
    for _ in [0:10000] do
      let (s, d) := srv.poll sim.now
      srv := s
      match d with
      | some d => sim := transmit net { sim with server := some srv } false d
      | none => break
    sim := { sim with server := some srv }
  pure sim

/-- The server application: echo every stream, finish when the client finishes. -/
def echo (c : Conn) : Conn := Id.run do
  let mut c := c
  let (c', _) := c.takeIncoming
  c := c'
  for (id, _) in c.streams.toList do
    let (c', data) := c.read id (c.readable id)
    c := c'.write id data
    if c.recvFinished id then c := c.finish id
    c := c.retire id
  pure c

def endpoint (retry : Bool) : Endpoint.Config :=
  { tls := serverTls, retry, tokenKey := ⟨Array.replicate 32 3⟩ }

def deliver (retry : Bool) (sim : Sim) (toServer : Bool) (d : ByteArray) : Sim :=
  if toServer then
    match sim.server with
    | some s => { sim with server := some (echo (s.recv sim.now d)) }
    | none =>
      let seed : Vector UInt8 32 := Vector.ofFn fun i => UInt8.ofNat (200 + i.val)
      match Endpoint.onUnknown (endpoint retry) "127.0.0.1:1".toUTF8 d sim.now ⟨#[7, 7, 7, 7, 7, 7, 7, 7]⟩ seed with
      | .drop => { sim with dropped := sim.dropped + 1 }
      | .retry pkt => { sim with wire := sim.wire.push (sim.now + 10000, false, pkt), retries := sim.retries + 1 }
      | .accept s _ => { sim with server := some (echo (s.recv sim.now d)) }
  else { sim with client := sim.client.recv sim.now d }

def decision : Endpoint.Decision → String
  | .drop => "drop"
  | .retry _ => "retry"
  | .accept _ _ => "accept"

/-- Retry tokens: a client's second Initial is accepted while its token is fresh, and dropped once
the token has expired, before it was issued, or from another address. -/
def tokenChecks : IO Nat := do
  let cfg := endpoint true
  let addr := "127.0.0.1:1".toUTF8
  let fresh : ByteArray := ⟨#[7, 7, 7, 7, 7, 7, 7, 7]⟩
  let seed : Vector UInt8 32 := Vector.ofFn fun i => UInt8.ofNat (200 + i.val)
  let t := 5_000_000
  let client ← match Conn.newClient {} clientTls seed ⟨#[1, 2, 3, 4, 5, 6, 7, 8]⟩
      ⟨#[9, 8, 7, 6, 5, 4, 3, 2]⟩ t with
    | .ok c => pure c
    | .error a => throw (IO.userError s!"client: {repr a}")
  let (client, some first) := client.poll t | throw (IO.userError "no Initial")
  let .retry pkt := Endpoint.onUnknown cfg addr first t fresh seed
    | throw (IO.userError "no Retry")
  let (_, some second) := (client.recv (t + 10_000) pkt).poll (t + 10_000)
    | throw (IO.userError "no Initial after Retry")
  let odcid := (first.extract 6 (6 + (first.get! 5).toNat))
  let token := Endpoint.makeToken cfg.tokenKey addr odcid fresh t
  let flipped := token.set! (1 + odcid.size + 7) (token.get! (1 + odcid.size + 7) ^^^ 1)
  let cases : List (String × String × String) := [
    ("fresh token", decision (Endpoint.onUnknown cfg addr second (t + 1_000_000) fresh seed), "accept"),
    ("token at its lifetime", decision (Endpoint.onUnknown cfg addr second (t + cfg.tokenLifetime) fresh seed), "accept"),
    ("expired token", decision (Endpoint.onUnknown cfg addr second (t + cfg.tokenLifetime + 1) fresh seed), "drop"),
    ("token from the future", decision (Endpoint.onUnknown cfg addr second (t - 1) fresh seed), "drop"),
    ("token from another address", decision (Endpoint.onUnknown cfg "127.0.0.1:2".toUTF8 second (t + 1000) fresh seed), "drop"),
    ("token checks", toString (Endpoint.checkToken cfg.tokenKey addr fresh token t cfg.tokenLifetime == some odcid), "true"),
    ("token with a flipped issue time", toString (Endpoint.checkToken cfg.tokenKey addr fresh flipped t cfg.tokenLifetime).isSome, "false")]
  let mut failed := 0
  for (name, got, want) in cases do
    let ok := got == want
    IO.println s!"  {if ok then "ok  " else "FAIL"}  {name}: {got}"
    if !ok then failed := failed + 1
  pure failed

structure Outcome where
  ok : Bool
  detail : String
  millis : Nat

/-- Run the client application: payloads of `size` bytes on `streams` streams in turn. -/
def runTransfer (net : Net) (size streams : Nat) (seed : Nat) (retry : Bool) : IO Outcome := do
  let t0 ← IO.monoMsNow
  let cseed : Vector UInt8 32 := Vector.ofFn fun i => UInt8.ofNat (i.val + seed)
  let start := 1000000
  let client ← match Conn.newClient {} clientTls cseed ⟨#[1, 2, 3, 4, 5, 6, 7, 8]⟩
      ⟨#[9, 8, 7, 6, 5, 4, 3, 2]⟩ start with
    | .ok c => pure c
    | .error a => throw (IO.userError s!"client: {repr a}")
  let mut sim : Sim := { now := start, rng := { s := seed }, client }
  let payload := pattern size
  let mut done := 0
  let mut current : Option Nat := none
  let mut received := ByteArray.empty
  let mut failure : Option String := none
  for _ in [0:200000] do
    -- Client application.
    if sim.client.isEstablished && done < streams then
      match current with
      | none =>
        let (c, id) := sim.client.openStream
        sim := { sim with client := c }
        if let some id := id then
          sim := { sim with client := (sim.client.write id payload).finish id }
          current := some id
          received := ByteArray.empty
      | some id =>
        let (c, data) := sim.client.read id (sim.client.readable id)
        sim := { sim with client := c }
        received := received ++ data
        if sim.client.recvFinished id then
          if received != payload then
            failure := some s!"stream {id}: echo of {received.size} bytes differs"
            break
          sim := { sim with client := sim.client.retire id }
          done := done + 1
          current := none
    if done == streams then break
    if sim.client.isClosed then
      let srvReason := sim.server.bind (·.closeReason)
      failure := some s!"client closed: {repr sim.client.closeReason}, server: {repr srvReason}"
      break
    sim := flush net sim
    -- Advance to the next event.
    let arrivals := sim.wire.map (·.1)
    let timers := [sim.client.nextTimeout, sim.server.bind (·.nextTimeout)].filterMap id
    let next := (arrivals.toList ++ timers).foldl min (sim.now + 1000000)
    sim := { sim with now := max next sim.now }
    let (due, later) := sim.wire.partition (·.1 ≤ sim.now)
    sim := { sim with wire := later }
    -- Stable: datagrams with one arrival time keep their sending order.
    let ordered := (due.zipIdx.qsort fun (a, i) (b, j) => a.1 < b.1 || (a.1 == b.1 && i < j)).map (·.1)
    for (_, toServer, d) in ordered do
      sim := deliver retry sim toServer d
    if sim.client.nextTimeout.any (· ≤ sim.now) then
      sim := { sim with client := sim.client.onTimeout sim.now }
    if let some s := sim.server then
      if s.nextTimeout.any (· ≤ sim.now) then sim := { sim with server := some (echo (s.onTimeout sim.now)) }
  let t1 ← IO.monoMsNow
  let simulated := (sim.now - start) / 1000
  match failure with
  | some f => pure { ok := false, detail := f, millis := t1 - t0 }
  | none =>
    if done == streams then
      pure { ok := true, millis := t1 - t0,
             detail := s!"{size * streams} bytes, {sim.sentDatagrams} datagrams ({sim.dropped} dropped), {sim.retries} Retry, {simulated} ms simulated" }
    else pure { ok := false, millis := t1 - t0,
                detail := s!"stalled after {done} streams, established {sim.client.isEstablished}, {simulated} ms simulated" }

def main : IO UInt32 := do
  let mut failed ← tokenChecks
  let cases : List (String × Net × Nat × Nat) := [
    ("clean, 1 byte", ⟨0, 0, 0⟩, 1, 1),
    ("clean, empty stream", ⟨0, 0, 0⟩, 0, 1),
    ("clean, 100 kB", ⟨0, 0, 0⟩, 100000, 1),
    ("clean, 4 streams of 100 kB", ⟨0, 0, 0⟩, 100000, 4),
    ("clean, 3 MB", ⟨0, 0, 0⟩, 3000000, 1),
    ("5% loss, 10% reorder, 2% duplicates, 100 kB", ⟨5, 10, 2⟩, 100000, 1),
    ("10% loss, 20% reorder, 5% duplicates, 300 kB", ⟨10, 20, 5⟩, 300000, 2),
    ("5% loss, 3 MB", ⟨5, 5, 1⟩, 3000000, 1)]
  for (name, net, size, streams) in cases do
    for seed in [1, 2, 3] do
      let retry := seed != 3
      let o ← runTransfer net size streams seed retry
      IO.println s!"  {if o.ok then "ok  " else "FAIL"}  {name} (seed {seed}{if retry then ", Retry" else ""}): {o.detail}, {o.millis} ms"
      if !o.ok then failed := failed + 1
  IO.println (if failed == 0 then "all loopback transfers passed" else s!"{failed} loopback transfers failed")
  pure (if failed == 0 then 0 else 1)
