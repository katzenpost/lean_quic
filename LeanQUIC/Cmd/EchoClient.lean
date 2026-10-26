import LeanQUIC.UDP
import Cryptlib.Util.HexBytes

open LeanQUIC
open LeanQUIC.UDP
open Cryptlib.Util.HexBytes (hexStringToByteArray byteArrayToHex)

/-! `quic_echo_client --connect HOST:PORT --pin HEX64 [--payload-size N] [--streams K]`: opens
`K` streams one after another, sends `N` bytes on each (byte `i` is `i mod 251`), and checks the
echo. Prints `OK bytes=… group=X25519MLKEM768 suite=…` on success. -/

def argOf (args : List String) (name : String) : Option String :=
  match args.dropWhile (· != name) with
  | _ :: v :: _ => some v
  | _ => none

structure Progress where
  done : Nat := 0
  current : Option Nat := none
  received : ByteArray := ByteArray.empty
  failure : Option String := none

def main (args : List String) : IO UInt32 := do
  let some server := (argOf args "--connect").bind parseAddr
    | IO.eprintln "usage: quic_echo_client --connect 127.0.0.1:PORT --pin HEX64 [--payload-size N] [--streams K]"
      return 2
  let some pin := (argOf args "--pin").bind hexStringToByteArray | IO.eprintln "--pin must be hex"; return 2
  let size := ((argOf args "--payload-size").bind String.toNat?).getD 100000
  let streams := ((argOf args "--streams").bind String.toNat?).getD 1
  let payload : ByteArray := ⟨Array.ofFn fun i : Fin size => UInt8.ofNat (i.val % 251)⟩
  let tls : LeanTLS.Handshake.Client.Config :=
    { alpn := "h3".toUTF8, transportParams := ByteArray.empty, pins := [pin],
      schemes := if args.contains "--mldsa" then [.mldsa65] else [.ed25519, .mldsa65] }
  let st ← IO.mkRef ({} : Progress)
  let app (c : Conn) : IO (Conn × Option String) := do
    let mut c := c
    if !c.isEstablished then return (c, none)
    let mut p ← st.get
    for _ in [0:2] do
      if p.done == streams then
        let suite := (c.app.writeKeys.map (·.suite.cipherSuite.name)).getD "?"
        let auth := match c.tls.authScheme? with
          | some .mldsa65 => "ML-DSA-65" | some .ed25519 => "Ed25519" | none => "?"
        return (c, some s!"OK bytes={size * streams} group=X25519MLKEM768 suite={suite} auth={auth} keyupdates={c.keyUpdates}")
      match p.current with
      | none =>
        let (c', id) := c.openStream
        c := c'
        if let some id := id then
          c := (c.write id payload).finish id
          p := { p with current := some id, received := ByteArray.empty }
      | some id =>
        let (c', data) := c.read id (c.readable id)
        c := c'
        p := { p with received := p.received ++ data }
        if c.recvFinished id then
          if p.received != payload then
            st.set p
            throw (IO.userError s!"stream {id}: echo of {p.received.size} bytes differs")
          c := c.retire id
          p := { p with done := p.done + 1, current := none }
    st.set p
    pure (c, none)
  let keyUpdate := ((argOf args "--key-update").bind String.toNat?).getD 0
  match ← runClient { keyUpdateInterval := keyUpdate } tls server app with
  | .ok line =>
    IO.println line
    pure 0
  | .error e =>
    IO.eprintln s!"quic_echo_client: {e}"
    pure 1
