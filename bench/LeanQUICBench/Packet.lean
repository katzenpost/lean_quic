/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import LeanQUIC
import LeanBench

/-! # Packet protection of a 1200-byte 1-RTT packet, for each suite

The payload AEAD, the header protection mask and its application are timed apart, and then
together as `protect` and `openPacket`. Inputs are read from refs so the compiler cannot hoist the
work out of the timed action. -/

namespace LeanQUICBench.Packet

open LeanQUIC

def cfg : LeanBench.BenchConfig := { suite := some "quic", samples := 30, warmup := 3 }

def bytes (n : Nat) : ByteArray := ⟨Array.ofFn fun (i : Fin n) => (i.val * 7 % 251).toUInt8⟩

def suiteName : LeanTLS.Suite → String
  | .chacha20poly1305 => "chacha20-poly1305"
  | .aes128gcm => "aes-128-gcm"

def benches : IO (Array LeanBench.Bench) := do
  let pnLen := 2
  let pn ← IO.mkRef 1000
  let header ← IO.mkRef (shortHeader (bytes 8) false 1000 pnLen)
  -- 11 header bytes and a 16-byte tag around the payload make a 1200-byte packet.
  let payload ← IO.mkRef (bytes (1200 - 11 - tagSize))
  let out ← IO.mkRef ByteArray.empty
  let opened ← IO.mkRef (none : Option ByteArray)
  let openedPkt ← IO.mkRef (none : Option Opened)
  let maskOut ← IO.mkRef (Vector.replicate 5 (0 : UInt8))
  let mut bs := #[]
  for suite in [LeanTLS.Suite.chacha20poly1305, .aes128gcm] do
    let name := suiteName suite
    let keys ← IO.mkRef (Keys.ofSecret suite (bytes 32))
    let k ← keys.get
    let sealed ← IO.mkRef (sealPayload k 1000 (← header.get) (← payload.get))
    let pkt ← IO.mkRef (protect k false (← header.get) 1000 pnLen (← payload.get))
    unless (← pkt.get).size == 1200 do throw (IO.userError s!"packet is {(← pkt.get).size} bytes")
    unless (openPacket k false (← pkt.get) 9 (some 999)).isSome do
      throw (IO.userError s!"{name}: the packet does not open")
    let sample ← IO.mkRef (sampleAt (← pkt.get) 13)
    bs := bs.push { name := s!"{name} sealPayload 1200B packet", config := cfg,
                    action := do out.set (sealPayload (← keys.get) (← pn.get) (← header.get) (← payload.get)) }
    bs := bs.push { name := s!"{name} openPayload 1200B packet", config := cfg,
                    action := do opened.set (openPayload (← keys.get) (← pn.get) (← header.get) (← sealed.get)) }
    bs := bs.push { name := s!"{name} header protection mask", config := cfg,
                    action := do maskOut.set (mask (← keys.get) (← sample.get)) }
    bs := bs.push { name := s!"{name} protect 1200B packet", config := cfg,
                    action := do
                      out.set (protect (← keys.get) false (← header.get) (← pn.get) pnLen (← payload.get)) }
    bs := bs.push { name := s!"{name} openPacket 1200B packet", config := cfg,
                    action := do openedPkt.set (openPacket (← keys.get) false (← pkt.get) 9 (some 999)) }
  let m ← IO.mkRef (Vector.ofFn fun (i : Fin 5) => (i.val * 37 + 5).toUInt8)
  for size in [75, 300, 1200] do
    let p ← IO.mkRef (bytes size)
    bs := bs.push { name := s!"applyMask {size}B packet", config := cfg,
                    action := do out.set (applyMask false (← p.get) 9 2 (← m.get)) }
  pure bs

end LeanQUICBench.Packet
