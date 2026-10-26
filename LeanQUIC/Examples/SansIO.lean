import LeanQUIC

open LeanQUIC
open Cryptlib.Util.Bytes (ofVector toVecN)

/-! A client and a server connection talking with no sockets at all: the "network" is a
function call. This is how lean_quic is tested, and how an application can run QUIC over any
transport. Run: `lake exe example_sansio`. -/

def key : Vector UInt8 32 := Vector.replicate 32 1
def cert : ByteArray :=
  LeanTLS.X509.selfSigned (fun m => ofVector (LeanTLS.Handshake.ed25519.sign key m ()).1)
    (ofVector (LeanTLS.Handshake.ed25519.pub key)) (ByteArray.mk (Array.replicate 16 1)) 0 86400
def pin : ByteArray := match LeanTLS.X509.parseLeaf cert with
  | .ok leaf => LeanTLS.KeySchedule.hash leaf.spki
  | .error _ => .empty

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
  let ctls : LeanTLS.Handshake.Client.Config :=
    { alpn := "h3".toUTF8, transportParams := .empty, pins := [pin] }
  let stls : LeanTLS.Handshake.Server.Config :=
    { alpn := "h3".toUTF8, transportParams := .empty, signingKey := key, certificate := cert }
  let cid (b : UInt8) : ByteArray := ByteArray.mk (Array.replicate 8 b)
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
