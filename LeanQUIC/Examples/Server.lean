import LeanQUIC.UDP
import Cryptlib.Util.HexBytes

open LeanQUIC LeanQUIC.UDP
open Cryptlib.Util.Bytes (toVecN)

/-! A server that answers each stream with `hello, ` and what the client sent.
Run: `lake exe example_server`; it prints the pin clients need. -/

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
    IO.println s!"listening; pin {Cryptlib.Util.HexBytes.byteArrayToHex ((spkiPin cert).getD .empty)}"
    (← IO.getStdout).flush
