import LeanQUIC.UDP
import Cryptlib.Util.HexBytes

open LeanQUIC LeanQUIC.UDP

/-! A client that sends its name on one stream and prints the reply.
Run: `lake exe example_client <pin>` with the pin `example_server` printed. -/

def main (args : List String) : IO UInt32 := do
  let some pin := args.head?.bind Cryptlib.Util.HexBytes.hexStringToByteArray
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
