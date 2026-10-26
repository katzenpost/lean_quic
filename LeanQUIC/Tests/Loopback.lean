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
  /-- Both sides' connection configuration. -/
  cfg : LeanQUIC.Config := {}

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

def endpoint (retry : Bool) (quic : LeanQUIC.Config := {}) : Endpoint.Config :=
  { quic, tls := serverTls, retry, tokenKey := ⟨Array.replicate 32 3⟩ }

def deliver (retry : Bool) (sim : Sim) (toServer : Bool) (d : ByteArray) : Sim :=
  if toServer then
    match sim.server with
    | some s => { sim with server := some (echo (s.recv sim.now d)) }
    | none =>
      let seed : Vector UInt8 32 := Vector.ofFn fun i => UInt8.ofNat (200 + i.val)
      match Endpoint.onUnknown (endpoint retry sim.cfg) "127.0.0.1:1".toUTF8 d sim.now ⟨#[7, 7, 7, 7, 7, 7, 7, 7]⟩ seed with
      | .drop => { sim with dropped := sim.dropped + 1 }
      | .retry pkt => { sim with wire := sim.wire.push (sim.now + 10000, false, pkt), retries := sim.retries + 1 }
      | .reset pkt => { sim with wire := sim.wire.push (sim.now + 10000, false, pkt) }
      | .accept s _ => { sim with server := some (echo (s.recv sim.now d)) }
  else { sim with client := sim.client.recv sim.now d }

/-- Run a clean network until nothing is in flight and both sides are established. -/
def settle (sim : Sim) : IO Sim := do
  let mut sim := sim
  for _ in [0:100] do
    sim := flush ⟨0, 0, 0⟩ sim
    if sim.wire.isEmpty && sim.client.isEstablished && (sim.server.any (·.isEstablished)) then break
    sim := { sim with now := (sim.wire.map (·.1)).foldl min (sim.now + 1000) }
    let (due, later) := sim.wire.partition (·.1 ≤ sim.now)
    sim := { sim with wire := later }
    for (_, toServer, d) in due do
      sim := deliver false sim toServer d
  pure sim

/-- A client and server connected over a clean network, and nothing left in flight. -/
def connected (cfg : LeanQUIC.Config := {}) : IO Sim := do
  let cseed : Vector UInt8 32 := Vector.ofFn fun i => UInt8.ofNat (i.val + 40)
  let client ← match Conn.newClient cfg clientTls cseed ⟨#[1, 2, 3, 4, 5, 6, 7, 8]⟩
      ⟨#[9, 8, 7, 6, 5, 4, 3, 2]⟩ 1000000 with
    | .ok c => pure c
    | .error a => throw (IO.userError s!"client: {repr a}")
  settle { now := 1000000, rng := { s := 1 }, client, cfg }

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

/-- Delayed acknowledgments (RFC 9000 §13.2): a receiver handed in-order packets one at a time
acknowledges every second one, and a lone packet only once `max_ack_delay` has passed. -/
def ackChecks : IO Nat := do
  let sim ← connected
  let some srv := sim.server | throw (IO.userError "no server")
  let now := sim.now + 100000
  let mut failed := 0
  -- Packets delivered and answered one by one.
  let (c, id) := sim.client.openStream
  let some id := id | throw (IO.userError "no stream")
  let (cl, ds) := drain ((c.write id (pattern 11000))) now
  let mut s := srv
  for d in ds do
    s := (drain (s.recv now d) now).1
  let acks := s.acksSent - srv.acksSent
  let okEvery := ds.size ≥ 8 && acks == ds.size / 2
  IO.println s!"  {if okEvery then "ok  " else "FAIL"}  {ds.size} packets in order: {acks} ACKs"
  if !okEvery then failed := failed + 1
  -- One more packet on its own: no ACK until max_ack_delay.
  let (c2, id2) := cl.openStream
  let some id2 := id2 | throw (IO.userError "no stream")
  let (_, one) := drain ((c2.write id2 (pattern 10)).finish id2) now
  let s0 := (drain s now).1
  let (s1, out1) := drain (one.foldl (fun s d => s.recv now d) s0) now
  let deadline := s1.nextTimeout
  let (s2, out2) := drain (s1.onTimeout (now + 25000)) (now + 25000)
  let okDelay := out1.isEmpty && deadline == some (now + 25000) && out2.size == 1 &&
    s2.acksSent == s0.acksSent + 1
  IO.println s!"  {if okDelay then "ok  " else "FAIL"}  a lone packet: {out1.size} datagrams at once, deadline +{(deadline.getD now) - now} µs, {out2.size} at the deadline"
  if !okDelay then failed := failed + 1
  pure failed

/-- Key update rules (RFC 9001 §6): no update before the handshake is confirmed, and a 1-RTT
packet that fails authentication is counted. -/
def keyChecks : IO Nat := do
  let sim ← connected
  let some srv := sim.server | throw (IO.userError "no server")
  let now := sim.now + 100000
  let mut failed := 0
  let fresh ← match Conn.newClient {} clientTls (Vector.replicate 32 5) ⟨#[1, 2, 3, 4, 5, 6, 7, 8]⟩
      ⟨#[9, 8, 7, 6, 5, 4, 3, 2]⟩ now with
    | .ok c => pure c
    | .error a => throw (IO.userError s!"client: {repr a}")
  let early := (fresh.updateKeys now).keyUpdates == 0
  IO.println s!"  {if early then "ok  " else "FAIL"}  no key update before the handshake is confirmed"
  if !early then failed := failed + 1
  let (c, id) := sim.client.openStream
  let some id := id | throw (IO.userError "no stream")
  let (_, ds) := drain ((c.write id (pattern 100)).finish id) now
  let some d := ds[0]? | throw (IO.userError "no datagram")
  let tampered := d.set! (d.size - 1) (d.get! (d.size - 1) ^^^ 1)
  let s := srv.recv now tampered
  let counted := s.authFailures == srv.authFailures + 1 && !s.isClosed
  IO.println s!"  {if counted then "ok  " else "FAIL"}  a tampered 1-RTT packet counts as an authentication failure"
  if !counted then failed := failed + 1
  pure failed

/-- Connection IDs (RFC 9000 §5.1, §10.3): each side offers the other four, a client can move to a
fresh one of the server's, and a server that lost the connection resets the client statelessly. -/
def cidChecks : IO Nat := do
  let cfg : LeanQUIC.Config := { resetKey := ⟨Array.replicate 32 9⟩ }
  let sim ← connected cfg
  let some srv := sim.server | throw (IO.userError "no server")
  let mut failed := 0
  let offered := sim.client.peerCids.length == 4 && srv.peerCids.length == 4 &&
    srv.activeLocalCids.length == 4 && sim.client.activeLocalCids.length == 4
  IO.println s!"  {if offered then "ok  " else "FAIL"}  connection IDs offered: client knows {sim.client.peerCids.length} of the server's, server {srv.peerCids.length} of the client's"
  if !offered then failed := failed + 1
  -- The client moves to another of the server's connection IDs and sends on it.
  let old := sim.client.remoteCid
  let (c, id) := sim.client.rotateRemoteCid.openStream
  let some id := id | throw (IO.userError "no stream")
  let sim ← settle { sim with client := (c.write id (pattern 3000)).finish id }
  let some srv := sim.server | throw (IO.userError "no server")
  let (cr, data) := sim.client.read id (sim.client.readable id)
  let echoed := data == pattern 3000 && cr.recvFinished id
  let moved := sim.client.remoteCid != old && !srv.isLocalCid old && srv.activeLocalCids.length == 4 &&
    srv.nextLocalSeq == 5 && echoed
  IO.println s!"  {if moved then "ok  " else "FAIL"}  the client moves to a new connection ID: old retired by the server, replaced, {data.size} bytes echoed"
  if !moved then failed := failed + 1
  -- The server forgets the connection; the client's next packet draws a stateless reset.
  let (c, id) := sim.client.openStream
  let some id := id | throw (IO.userError "no stream")
  let (c, ds) := drain ((c.write id (pattern 500)).finish id) sim.now
  let some d := ds[0]? | throw (IO.userError "no datagram")
  let reset := match Endpoint.onUnknown (endpoint true cfg) "127.0.0.1:1".toUTF8 d sim.now
      ⟨#[7, 7, 7, 7, 7, 7, 7, 7]⟩ (Vector.replicate 32 3) with
    | .reset pkt => some pkt
    | _ => none
  let ok := match reset with
    | some pkt =>
      let c := c.recv (sim.now + 10000) pkt
      pkt.size < d.size && c.closeReason.any (·.2.2 == "stateless reset") && (c.poll (sim.now + 10000)).2.isNone
    | none => false
  IO.println s!"  {if ok then "ok  " else "FAIL"}  a server without the connection resets it statelessly, and the client drains"
  if !ok then failed := failed + 1
  pure failed

structure Outcome where
  ok : Bool
  detail : String
  millis : Nat
  /-- ACK frames sent and ack-eliciting packets received, by the client and by the server. -/
  acks : (Nat × Nat) × (Nat × Nat) := ((0, 0), (0, 0))

/-- Run the client application: payloads of `size` bytes on `streams` streams in turn. -/
def runTransfer (net : Net) (size streams : Nat) (seed : Nat) (retry : Bool)
    (cfg : LeanQUIC.Config := {}) : IO Outcome := do
  let t0 ← IO.monoMsNow
  let cseed : Vector UInt8 32 := Vector.ofFn fun i => UInt8.ofNat (i.val + seed)
  let start := 1000000
  let client ← match Conn.newClient cfg clientTls cseed ⟨#[1, 2, 3, 4, 5, 6, 7, 8]⟩
      ⟨#[9, 8, 7, 6, 5, 4, 3, 2]⟩ start with
    | .ok c => pure c
    | .error a => throw (IO.userError s!"client: {repr a}")
  let mut sim : Sim := { now := start, rng := { s := seed }, client, cfg }
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
      let srv := sim.server.map (fun s => (s.acksSent, s.elicitingRecv)) |>.getD (0, 0)
      let cli := (sim.client.acksSent, sim.client.elicitingRecv)
      let updates := (sim.client.keyUpdates, (sim.server.map (·.keyUpdates)).getD 0)
      pure { ok := cfg.keyUpdateInterval == 0 || (updates.1 > 0 && updates.2 > 0),
             millis := t1 - t0, acks := (cli, srv),
             detail := s!"{size * streams} bytes, {sim.sentDatagrams} datagrams ({sim.dropped} dropped), {sim.retries} Retry, {simulated} ms simulated, ACKs {cli.1}/{cli.2} client, {srv.1}/{srv.2} server, key updates {updates.1} client, {updates.2} server" }
    else pure { ok := false, millis := t1 - t0,
                detail := s!"stalled after {done} streams, established {sim.client.isEstablished}, {simulated} ms simulated" }

def main : IO UInt32 := do
  let mut failed ← ackChecks
  failed := failed + (← keyChecks)
  failed := failed + (← cidChecks)
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
  -- Key updates every 50 packets, by both sides, clean and lossy.
  for (name, net, size) in [("clean, 1 MB", (⟨0, 0, 0⟩ : Net), 1000000),
      ("5% loss, 10% reorder, 1 MB", ⟨5, 10, 1⟩, 1000000)] do
    for seed in [1, 2] do
      let o ← runTransfer net size 1 seed true { keyUpdateInterval := 50 }
      IO.println s!"  {if o.ok then "ok  " else "FAIL"}  {name}, key update every 50 packets (seed {seed}): {o.detail}, {o.millis} ms"
      if !o.ok then failed := failed + 1
  IO.println (if failed == 0 then "all loopback transfers passed" else s!"{failed} loopback transfers failed")
  pure (if failed == 0 then 0 else 1)
