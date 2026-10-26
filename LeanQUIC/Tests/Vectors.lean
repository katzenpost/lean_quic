import Lean.Data.Json
import LeanQUIC
import LeanTLS.Messages
import Cryptlib.Util.HexBytes

open Lean
open LeanQUIC
open LeanTLS.KeySchedule (quicKeys quicNextSecret)
open Cryptlib.Util.HexBytes (hexStringToByteArray byteArrayToHex)

/-! RFC 9001 Appendix A packet protection byte for byte: Initial secrets and keys, the client and
server Initial packets protected and opened, the Retry integrity tag, and the ChaCha20-Poly1305
short header packet. With RFC 9000's varint and packet number examples, and the frames and
transport parameters inside those packets. -/

def hex! (s : String) : ByteArray := (hexStringToByteArray s).getD ByteArray.empty

def check (r : IO.Ref Nat) (name : String) (got want : ByteArray) : IO Unit := do
  if got == want then IO.println s!"  ok    {name}"
  else
    r.modify (· + 1)
    IO.println s!"  FAIL  {name}\n        got  {byteArrayToHex got}\n        want {byteArrayToHex want}"

def ok (r : IO.Ref Nat) (name : String) (b : Bool) : IO Unit := do
  if b then IO.println s!"  ok    {name}" else
    r.modify (· + 1)
    IO.println s!"  FAIL  {name}"

def main : IO UInt32 := do
  let r ← IO.mkRef 0
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile "testdata/rfc9001_appendix_a.json"))
  let vs ← IO.ofExcept (j.getObjVal? "vectors")
  let v (k : String) : IO ByteArray := do
    pure (hex! (← IO.ofExcept ((← IO.ofExcept (vs.getObjVal? k)).getStr?)))
  let dcid ← v "dcid"

  IO.println "RFC 9000 Appendix A"
  for (enc, val) in [("c2197c5eff14e88c", 151288809941952652), ("9d7f3e7d", 494878333),
                     ("7bbd", 15293), ("25", 37), ("4025", 37)] do
    ok r s!"varint {enc} = {val}" (LeanTLS.Wire.Parser.run varint (hex! enc) == .ok val)
  for val in [0, 37, 63, 64, 15293, 16383, 16384, 494878333, 2 ^ 30, 151288809941952652, VarInt.max] do
    ok r s!"varint {val} round trip" (LeanTLS.Wire.Parser.run varint (encodeVarInt val) == .ok val)
  ok r "decode packet number 0x9b32 after 0xa82f30ea" (decodePn (some 0xa82f30ea) 0x9b32 2 == 0xa82f9b32)
  ok r "encode 0xac5c02 after 0xabe8b3 in 2 bytes" (pnLength 0xac5c02 (some 0xabe8b3) == 2)
  ok r "encode 0xace8fe after 0xabe8b3 in 3 bytes" (pnLength 0xace8fe (some 0xabe8b3) == 3)

  IO.println "RFC 9001 A.1 keys"
  let (cs, ss) := initialSecrets dcid
  check r "client initial secret" cs (← v "client_initial_secret")
  check r "server initial secret" ss (← v "server_initial_secret")
  let ck := quicKeys cs 16
  let sk := quicKeys ss 16
  check r "client key" ck.key (← v "client_key")
  check r "client iv" ck.iv (← v "client_iv")
  check r "client hp" ck.hp (← v "client_hp")
  check r "server key" sk.key (← v "server_key")
  check r "server iv" sk.iv (← v "server_iv")
  check r "server hp" sk.hp (← v "server_hp")
  let (clientKeys, serverKeys) := initialKeys dcid

  IO.println "RFC 9001 A.2 client Initial"
  let crypto ← v "client_crypto_frame"
  let payload := crypto ++ ⟨Array.replicate (1162 - crypto.size) 0⟩
  let cpkt ← v "client_packet"
  check r "protect" (protect clientKeys true (← v "client_header") 2 4 payload) cpkt
  match parseHeader cpkt 0 0 with
  | some (.long .initial 1 d s t pnOffset, len) =>
    ok r "parse header" (d == dcid && s.size == 0 && t.size == 0 && pnOffset == 18 && len == 1200)
    match openPacket clientKeys true cpkt pnOffset none with
    | some o =>
      ok r "open: packet number 2" (o.pn == 2)
      check r "open: payload" o.payload payload
      match Frame.parseAll o.payload with
      | some #[.crypto 0 ch, .padding n] =>
        ok r "frames: CRYPTO then PADDING" (n == 1162 - crypto.size)
        let tps := match LeanTLS.Wire.Parser.run LeanTLS.Messages.clientHello (ch.extract 4 ch.size) with
          | .ok hello => (LeanTLS.Messages.find hello.extensions 0x39).bind TransportParams.decode
          | .error _ => none
        match tps with
        | some p =>
          ok r "transport parameters in the ClientHello" (p.initialMaxData == VarInt.max &&
            p.initialMaxStreamDataBidiLocal == 0xffff && p.initialMaxStreamsBidi == 16 &&
            p.initialSourceConnectionId == some dcid && p.maxIdleTimeout == 30000)
          ok r "transport parameters round trip"
            ((TransportParams.decode p.encode).map (·.encode.data) == some p.encode.data)
        | none => ok r "transport parameters in the ClientHello" false
      | _ => ok r "frames: CRYPTO then PADDING" false
    | none => ok r "open" false
  | _ => ok r "parse header" false
  ok r "open with the server's keys fails" ((openPacket serverKeys true cpkt 18 none).isNone)
  ok r "open a corrupted packet fails" ((openPacket clientKeys true (cpkt.set! 1000 0) 18 none).isNone)

  IO.println "RFC 9001 A.3 server Initial"
  let spayload ← v "server_payload"
  let spkt ← v "server_packet"
  check r "protect" (protect serverKeys true (← v "server_header") 1 2 spayload) spkt
  match parseHeader spkt 0 0 with
  | some (.long .initial _ _ _ _ pnOffset, _) =>
    match openPacket serverKeys true spkt pnOffset none with
    | some o =>
      ok r "open: packet number 1" (o.pn == 1)
      check r "open: payload" o.payload spayload
      match Frame.parseAll o.payload with
      | some #[.ack [(0, 0)] 0, .crypto 0 _] => ok r "frames: ACK of packet 0, then CRYPTO" true
      | _ => ok r "frames: ACK of packet 0, then CRYPTO" false
    | none => ok r "open" false
  | _ => ok r "parse header" false

  IO.println "RFC 9001 A.4 Retry"
  let retry ← v "retry_packet"
  ok r "integrity tag verifies" (retryValid dcid retry)
  ok r "integrity tag fails for another connection ID" (!retryValid (dcid.set! 0 0) retry)
  check r "build" (retryPacket dcid ByteArray.empty (hex! "f067a5502a4262b5") "token".toUTF8) retry
  match parseHeader retry 0 0 with
  | some (.long .retry _ d s t _, _) =>
    ok r "parse" (d.size == 0 && s == hex! "f067a5502a4262b5" && t == "token".toUTF8)
  | _ => ok r "parse" false

  IO.println "RFC 9001 A.5 ChaCha20-Poly1305 short header"
  let secret ← v "chacha_secret"
  let k := quicKeys secret 32
  check r "key" k.key (← v "chacha_key")
  check r "iv" k.iv (← v "chacha_iv")
  check r "hp" k.hp (← v "chacha_hp")
  check r "ku" (quicNextSecret secret) (← v "chacha_ku")
  let keys := Keys.ofSecret .chacha20poly1305 secret
  let pn := 654360564
  let hdr ← v "chacha_unprotected_header"
  check r "header" (shortHeader ByteArray.empty false pn 3) hdr
  let pkt ← v "chacha_packet"
  check r "protect" (protect keys false hdr pn 3 ⟨#[1]⟩) pkt
  match openPacket keys false pkt 1 (some (pn - 1)) with
  | some o => ok r "open" (o.pn == pn && o.payload == ⟨#[1]⟩)
  | none => ok r "open" false

  IO.println "frames"
  let frames : List Frame := [.ping, .ack [(10, 20), (5, 7), (0, 1)] 3, .crypto 7 ⟨#[1, 2, 3]⟩,
    .stream 4 0 ⟨#[9]⟩ false, .stream 4 1000 ⟨#[9, 9]⟩ true, .maxData 99999, .maxStreamData 4 77,
    .maxStreams true 100, .newConnectionId 1 0 ⟨#[1, 2, 3, 4]⟩ ⟨Array.replicate 16 5⟩,
    .retireConnectionId 0, .connectionClose false 0x0a 6 "bad".toUTF8, .handshakeDone,
    .resetStream 4 1 10, .stopSending 4 1, .newToken ⟨#[1]⟩, .pathChallenge ⟨Array.replicate 8 1⟩]
  for f in frames do
    let enc := f.encode
    let back := (Frame.parseAll enc).map fun fs => fs.map Frame.encode
    ok r s!"round trip {byteArrayToHex (enc.extract 0 1)}" (back.map (·.toList.map (·.data)) == some [enc.data])
  ok r "ACK with an impossible range is refused" (Frame.parseAll (hex! "020a000105") |>.isNone)

  IO.println "sealer"
  let (ck, sk) := initialKeys (hex! "8394c8f03e515708")
  let build (pn : Nat) : ByteArray × Nat × ByteArray :=
    (shortHeader (hex! "0102030405060708") false pn 4, 4, ⟨Array.replicate 30 0⟩)
  let steps := [Sealer.Step.send false build, .rekey ck, .send false build, .send false build,
    .discard, .send false build, .rekey sk, .send false build]
  let (s, pns) := Sealer.init.run steps
  ok r "nothing is sealed without keys" ((Sealer.init.send false build).isNone)
  ok r "packet numbers continue across rekeys" (pns == [0, 1, 2] && s.nextPn == 3)
  ok r "nonces are distinct" ((pns.map (nonce ck.iv)).eraseDups.length == pns.length)
  match Sealer.init.rekey ck |>.send false build with
  | some (_, pn, pkt) =>
    let (hdr, pnLen, payload) := build pn
    ok r "send seals with protect" (pkt == protect ck false hdr pn pnLen payload)
  | none => ok r "send seals with protect" false

  let n ← r.get
  IO.println (if n == 0 then "all vectors passed" else s!"{n} checks failed")
  pure (if n == 0 then 0 else 1)
