# lean_quic

*QUIC version 1 in Lean 4, post-quantum.*

This library has not been audited by any third party.

QUIC (RFC 9000, 9001, 9002) over [lean_tls](https://github.com/katzenpost/lean_tls)'s TLS 1.3
handshake, negotiating the X25519MLKEM768 hybrid key exchange. The connection is a pure value:
`recv` gives it a datagram, `poll` asks for the next one to send, `onTimeout` reports a passed
deadline, and the time is always an argument. The only IO is `LeanQUIC.UDP`, a driver over
Lean's own `Std.Async.UDP`.

## Modules

* `VarInt`, `Packet`, `Frame`, `TransportParams`: the wire format and packet protection.
  `Packet.openPayload_sealPayload` carries the AEAD's correctness over to packets and
  `Packet.applyMask_applyMask` shows header protection undoes itself.
* `Sealer`: a space's write keys and packet number counter, the only way to seal a packet.
  `Sealer.run_nonces_nodup` proves that, through any sequence of key changes, no two packets of
  a space get the same nonce.
* `Recovery`: loss detection and NewReno congestion control (RFC 9002), with the congestion
  window's lower bound as a proof field of its state.
* `Buffers`: stream and CRYPTO reassembly and retransmission, its interval sets carrying their
  sortedness as proofs.
* `Connection`: the connection state machine. Stream data is accepted only once TLS has produced
  its evidence that the peer is authenticated.
* `UDP`, `Cmd/EchoServer`, `Cmd/EchoClient`: the driver and the interop executables.

## Using lean_quic

A connection is a value of type `Conn`. You never call into the network yourself. Your
application is a function from a `Conn` to a new `Conn`, and `LeanQUIC.UDP` calls it after
every datagram and timer. The three programs below are in `LeanQUIC/Examples/` and are built by
CI, so they stay in step with the code.

### A server

`runServer` listens on a UDP socket, sends every new client a Retry (as katzenpost's servers do),
and calls your application after each event on a connection. The application here answers each
stream with `hello, ` and whatever the client sent:

```lean
import LeanQUIC.UDP

open LeanQUIC LeanQUIC.UDP

/-- The application: pure, called after every event on a connection. -/
def greet (c : Conn) : Conn := Id.run do
  let (c, _) := c.takeIncoming          -- streams the client opened since last time
  let mut c := c
  for (id, _) in c.streams.toList do
    -- Once the whole name has arrived and before it is read, answer it.
    if c.recvComplete id && c.readable id > 0 then
      let (c', name) := c.read id (c.readable id)
      c := (c'.write id ("hello, ".toUTF8 ++ name)).finish id
    c := c.retire id                     -- forget streams both sides are done with
  pure c

def main : IO Unit := do
  let key := toVecN 32 (← randomBytes 32)  -- the server's Ed25519 identity
  let cert ← epochCertificate key          -- self-signed, katzenpost style
  let tls : LeanTLS.Handshake.Server.Config :=
    { alpn := "h3".toUTF8, transportParams := ByteArray.empty, signingKey := key, certificate := cert }
  let some listen := parseAddr "127.0.0.1:4433" | throw (IO.userError "bad address")
  runServer { tls, tokenKey := ← randomBytes 32 } listen greet do
    IO.println s!"listening; pin {byteArrayToHex ((spkiPin cert).getD .empty)}"
```

The server is authenticated by its key, not by a certificate authority: clients pin
`SHA-256(SubjectPublicKeyInfo)`, which `spkiPin` computes.

### A client

`runClient` connects and calls your application after every event until it returns `some`
result. Here the application keeps a little state in `IO.Ref`s: open a stream, send a name, and
collect the reply:

```lean
def main (args : List String) : IO UInt32 := do
  let some pin := args.head?.bind hexStringToByteArray
    | IO.eprintln "usage: example_client <pin>"; return 2
  let tls : LeanTLS.Handshake.Client.Config :=
    { alpn := "h3".toUTF8, transportParams := ByteArray.empty, pins := [pin] }
  let some server := parseAddr "127.0.0.1:4433" | return 2
  let stream ← IO.mkRef (none : Option Nat)
  let reply ← IO.mkRef ByteArray.empty
  -- Called after every event; returning `some` ends the connection.
  let app (c : Conn) : IO (Conn × Option String) := do
    if !c.isEstablished then return (c, none)   -- still handshaking
    match ← stream.get with
    | none =>
      let (c, id) := c.openStream
      let some id := id | return (c, none)       -- the server allows no more streams yet
      stream.set (some id)
      return ((c.write id "world".toUTF8).finish id, none)
    | some id =>
      let (c, data) := c.read id (c.readable id)
      reply.modify (· ++ data)
      if c.recvFinished id then
        return (c, some (String.fromUTF8! (← reply.get)))
      return (c, none)
  match ← runClient {} tls server app with
  | .ok text => IO.println text; pure 0          -- hello, world
  | .error e => IO.eprintln e; pure 1
```

```bash
lake exe example_server                  # listening; pin ac4b15f2…
lake exe example_client ac4b15f2…        # hello, world
```

`isEstablished` becomes true only once TLS has checked the server's pin, its signature and its
Finished; before that, `openStream` refuses and no stream data moves.

### Without sockets

Underneath, a connection is four pure functions: `recv now datagram` takes a datagram in,
`poll now` gives the next one out, and `nextTimeout` / `onTimeout now` handle timers, with time in
microseconds passed as an argument. So two connections can talk through nothing but function
calls, which is how lean_quic is tested, and how QUIC could run over another transport:

```lean
/-- Every datagram `a` has to send now, delivered to `b`. -/
def send (now : Nat) (a b : Conn) : Conn × Conn := Id.run do
  let mut a := a
  let mut b := b
  for _ in [0:1000] do
    let (a', d) := a.poll now
    a := a'
    match d with
    | some d => b := b.recv now d
    | none => break
  pure (a, b)

def main : IO Unit := do
  -- Time is an argument (µs); entropy is a 32-byte seed per connection.
  let .ok client := Conn.newClient {} ctls (Vector.replicate 32 2) (cid 1) (cid 2) 0
    | throw (IO.userError "TLS refused the configuration")
  let server := Conn.newServer {} stls (Vector.replicate 32 3) (cid 3) (cid 2) (cid 1) 0
  let mut (c, s) := (client, server)
  for step in [0:10] do
    let now := step * 1000
    (c, s) := send now c s
    (s, c) := send now s c
    if c.isEstablished && s.isEstablished then
      IO.println s!"handshake done after {step + 1} round trips"
      break
  -- Streams once established: the client writes, the server reads.
  let (c', some id) := c.openStream | throw (IO.userError "no stream")
  c := (c'.write id "ping".toUTF8).finish id
  (c, s) := send 20000 c s
  let (_, data) := s.read id (s.readable id)
  IO.println s!"server read {String.fromUTF8! data} on stream {id}"
```

```
$ lake exe example_sansio
handshake done after 2 round trips
server read ping on stream 0
```

### The stream API

| | |
|---|---|
| `c.openStream : Conn × Option Nat` | a new bidirectional stream, if the peer's limit allows |
| `c.write id data`, `c.finish id` | queue data; mark its end |
| `c.readable id`, `c.read id n : Conn × ByteArray` | bytes ready in order; take up to `n` |
| `c.recvComplete id` | the peer finished and every byte has arrived |
| `c.recvFinished id` | … and every byte has been read |
| `c.sendFinished id` | everything written, and the end, acknowledged |
| `c.takeIncoming : Conn × Array Nat` | streams the peer opened since the last call |
| `c.retire id` | drop a stream both sides are done with, freeing a slot for the peer |
| `c.close now` | close the connection with no error |

## Tests

```bash
make test       # RFC 9000/9001 vectors, recovery, buffers, in-process transfers
make axioms     # every theorem depends on Lean's own axioms only
make interop    # against quic-go through katzenpost's own QUIC transport, see interop/
```

* `LeanQUIC.Tests.Vectors`: RFC 9001 Appendix A byte for byte (Initial keys, client and server
  Initial packets, Retry, ChaCha20-Poly1305 short header) and RFC 9000's varint and packet number
  examples. `testdata/rfc9001_appendix_a.json` is extracted from the RFC text by
  `scripts/extract_rfc9001.py`.
* `LeanQUIC.Tests.Loopback`: a client and a server connection in process through a simulated
  network with loss, reordering and duplication, transferring up to 3 MB.
