import LeanQUIC.UDP
import Cryptlib.Util.HexBytes

open LeanQUIC
open LeanQUIC.UDP
open Cryptlib.Util.HexBytes (hexStringToByteArray byteArrayToHex)
open Cryptlib.Util.Bytes (toVecN)

/-! `quic_echo_server --listen 127.0.0.1:PORT --seed HEX64 [--no-retry]`: a QUIC echo server
authenticating with the Ed25519 key from `seed`, in the shape of katzenpost's QUIC transport (ALPN
`h3`, X25519MLKEM768, a Retry before every connection). Prints `SPKI-SHA256 <hex>` and `READY`,
then echoes every stream. -/

def argOf (args : List String) (name : String) : Option String :=
  match args.dropWhile (· != name) with
  | _ :: v :: _ => some v
  | _ => none

def main (args : List String) : IO UInt32 := do
  let some listen := (argOf args "--listen").bind parseAddr
    | IO.eprintln "usage: quic_echo_server --listen 127.0.0.1:PORT --seed HEX64"; return 2
  let some seed := (argOf args "--seed").bind hexStringToByteArray
    | IO.eprintln "--seed must be 64 hex digits"; return 2
  if seed.size != 32 then IO.eprintln "--seed must be 64 hex digits"; return 2
  let key := toVecN 32 seed
  let cert ← epochCertificate key
  let some pin := spkiPin cert | IO.eprintln "certificate does not parse"; return 1
  let tls : LeanTLS.Handshake.Server.Config :=
    { alpn := "h3".toUTF8, transportParams := ByteArray.empty, signingKey := key, certificate := cert }
  let keyUpdate := ((argOf args "--key-update").bind String.toNat?).getD 0
  let tokenKey ← randomBytes 32
  let cfg : Endpoint.Config :=
    { quic := { keyUpdateInterval := keyUpdate }, tls, tokenKey, retry := !args.contains "--no-retry" }
  runServer cfg listen echo do
    IO.println s!"SPKI-SHA256 {byteArrayToHex pin}"
    IO.println "READY"
    (← IO.getStdout).flush
  pure 0
