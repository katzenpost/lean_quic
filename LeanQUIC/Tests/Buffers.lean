/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import LeanQUIC.Buffers

/-! # Buffer tests -/

open LeanQUIC.Buffers

namespace LeanQUIC.Tests.Buffers

/-- Stream byte `i` is `i % 251`. -/
def pat (off len : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity len
  for i in [off:off + len] do
    b := b.push (i % 251).toUInt8
  return b

def isPat (off : Nat) (b : ByteArray) : Bool := Id.run do
  for i in [0:b.size] do
    if b[i]! != ((off + i) % 251).toUInt8 then return false
  return true

structure Lcg where
  x : UInt64

def Lcg.next (g : Lcg) (n : Nat) : Nat × Lcg :=
  let x := g.x * 6364136223846793005 + 1442695040888963407
  ((x >>> 33).toNat % n, ⟨x⟩)

def check (fails : IO.Ref Nat) (name : String) (ok : Bool) : IO Unit := do
  unless ok do
    IO.println s!"FAIL: {name}"
    fails.modify (· + 1)

def ins! (r : Recv) (off : Nat) (d : ByteArray) (fin : Bool := false) : Recv :=
  match r.insert off d fin with
  | .ok r => r
  | .error _ => r

def insErr (r : Recv) (off : Nat) (d : ByteArray) (fin : Bool := false) : Option Error :=
  match r.insert off d fin with
  | .ok _ => none
  | .error e => some e

def insOk (r : Recv) (off : Nat) (d : ByteArray) (fin : Bool := false) : Bool :=
  (insErr r off d fin).isNone

def recvTests (check : String → Bool → IO Unit) : IO Unit := do
  -- in order
  let r := ins! (ins! (Recv.init 1000) 0 (pat 0 10)) 10 (pat 10 10)
  check "in-order readable" (r.readable == 20)
  let (r, b) := r.read 15
  check "in-order read" (b.size == 15 && isPat 0 b && r.readOffset == 15 && r.readable == 5)
  let (r, b) := r.read 100
  check "in-order rest" (b.size == 5 && isPat 15 b && r.readable == 0 && r.readOffset == 20)
  -- out of order
  let r := ins! (Recv.init 1000) 10 (pat 10 10)
  check "ooo hole" (r.readable == 0 && r.highestOffset == 20)
  let r := ins! r 0 (pat 0 10)
  let (r, b) := r.read 100
  check "ooo filled" (b.size == 20 && isPat 0 b && r.readable == 0)
  -- duplicates and overlaps
  let r := [(5, 10), (0, 8), (12, 18), (40, 5), (0, 30), (3, 1), (29, 12), (44, 6)].foldl
    (fun r (o, n) => ins! r o (pat o n)) (Recv.init 1000)
  let (r, b) := r.read 1000
  check "overlaps" (b.size == 50 && isPat 0 b)
  let r := ins! r 10 (pat 10 20)
  check "duplicate below read offset" (r.readable == 0 && r.readOffset == 50)
  let r := ins! r 45 (pat 45 10)
  let (_, b) := r.read 1000
  check "straddling read offset" (b.size == 5 && isPat 50 b)
  -- random chunking with overlaps
  let mut g : Lcg := ⟨7⟩
  let mut rr := Recv.init 100000
  for _ in [0:3000] do
    let (o, g') := g.next 20000; g := g'
    let (n, g') := g.next 300; g := g'
    rr := ins! rr o (pat o (min n (20000 - o)))
  rr := ins! rr 0 (pat 0 20000)
  let (r', b) := rr.read 100000
  check "random overlaps" (b.size == 20000 && isPat 0 b && r'.readable == 0)
  -- FIN
  let r := ins! (Recv.init 1000) 0 (pat 0 10) true
  check "fin final size" (r.finalSize == some 10 && !r.isFinished)
  check "data past final size" (insErr r 10 (pat 10 1) == some .finalSize)
  check "changed final size" (insErr r 0 (pat 0 5) true == some .finalSize)
  check "same final size again" (insOk r 0 (pat 0 10) true)
  check "fin-only same size" (insOk r 10 .empty true)
  check "data within final size" (insOk r 2 (pat 2 8))
  let (r, b) := r.read 4
  check "not finished mid-read" (b.size == 4 && !r.isFinished)
  let (r, _) := r.read 100
  check "finished" r.isFinished
  let r := ins! (Recv.init 1000) 20 (pat 20 10)
  check "final size below received" (insErr r 0 (pat 0 10) true == some .finalSize)
  let r := ins! (ins! (Recv.init 1000) 0 (pat 0 10)) 10 .empty true
  let (r, b) := r.read 100
  check "fin-only frame" (b.size == 10 && r.isFinished)
  let r := ins! (Recv.init 1000) 0 .empty true
  check "empty stream" (r.isFinished && r.finalSize == some 0)
  -- flow control
  let r := Recv.init 100
  check "past limit" (insErr r 90 (pat 90 11) == some .flowControl)
  check "up to limit" (insOk r 90 (pat 90 10))
  let r := r.setLimit 50
  check "limit not lowered" (r.limit == 100)
  let r := r.setLimit 200
  check "limit raised" (r.limit == 200 && insOk r 150 (pat 150 50)
    && insErr r 150 (pat 150 51) == some .flowControl)
  let big := 2 ^ 62
  let r := ins! (Recv.init big) (2 ^ 61) (pat 0 100)
  check "huge offset sparse" (r.readable == 0 && r.highestOffset == 2 ^ 61 + 100)
  -- CRYPTO style
  let c := Recv.initCrypto 4096
  check "crypto cap" (insErr c 4000 (pat 4000 100) == some .bufferExceeded)
  let c := ins! (ins! (ins! c 600 (pat 600 400)) 0 (pat 0 300)) 300 (pat 300 300)
  let (c, b) := c.read 4096
  check "crypto reassembly" (b.size == 1000 && isPat 0 b && c.finalSize == none && !c.isFinished)

def sendTests (check : String → Bool → IO Unit) : IO Unit := do
  let s := Send.init.write (pat 0 10)
  let (p, s) := s.next 4 100
  check "first chunk" (match p with | some (0, d, false) => d.size == 4 && isPat 0 d | _ => false)
  let (p, s) := s.next 100 7
  check "flow limited" (match p with | some (4, d, false) => d.size == 3 | _ => false)
  let (p, s1) := s.next 100 7
  check "blocked" (p.isNone && s1.hasPending)
  let s := s.finish
  let (p, s) := s.next 100 100
  check "fin with last byte" (match p with | some (7, d, true) => d.size == 3 && isPat 7 d | _ => false)
  let (p, s) := s.next 100 100
  check "nothing more" (p.isNone && !s.hasPending)
  let s := s.onAcked 3 3 false
  let s := s.onLost 0 10 true
  let (p, s) := s.next 100 100
  check "lost skips acked 1" (match p with | some (0, d, false) => d.size == 3 | _ => false)
  let (p, s) := s.next 100 100
  check "lost skips acked 2" (match p with | some (6, d, true) => d.size == 4 && isPat 6 d | _ => false)
  let s := s.onAcked 0 10 true
  check "all acked" (s.isAllAcked && s.buffered == 0 && !s.hasPending)
  -- FIN alone, and FIN retransmission
  let s := (Send.init.write (pat 0 5))
  let (_, s) := s.next 100 100
  let s := s.finish
  let (p, s) := s.next 100 100
  check "fin-only" (match p with | some (5, d, true) => d.size == 0 | _ => false)
  let s := s.onAcked 0 5 false
  check "fin unacked" (!s.isAllAcked)
  let s := s.onLost 5 0 true
  let (p, s) := s.next 100 100
  check "fin retransmitted" (match p with | some (5, d, true) => d.size == 0 | _ => false)
  let s := s.onAcked 5 0 true
  check "fin acked" s.isAllAcked
  let s := s.onLost 0 5 true
  check "loss after ack ignored" (!s.hasPending)
  -- empty stream
  let (p, s) := Send.init.finish.next 100 0
  check "empty stream fin" (match p with | some (0, d, true) => d.size == 0 | _ => false)
  check "empty stream acked" (s.onAcked 0 0 true).isAllAcked

/-- Push 3 MB through a lossy, reordering, duplicating channel. With `window`, the receiver
starts with that much credit and raises it as it reads. -/
def simulate (check : String → Bool → IO Unit) (seed : UInt64) (window : Option Nat) :
    IO Unit := do
  let total := 3 * 1024 * 1024
  let src := pat 0 total
  let mut s := Send.init
  let mut w := 0
  while w < total do
    let n := min 16384 (total - w)
    s := s.write (src.extract w (w + n))
    w := w + n
  s := s.finish
  let mut r := Recv.init (window.getD (2 ^ 62))
  let mut g : Lcg := ⟨seed⟩
  let mut out := ByteArray.emptyWithCapacity total
  let mut lateAcks : Array (Nat × Nat × Bool) := #[]
  let mut ok := true
  let mut credit := r.limit
  let mut rounds := 0
  let mut maxBuf := 0
  while rounds < 100000 && !(s.isAllAcked && r.isFinished) do
    rounds := rounds + 1
    let mut batch : Array (Nat × ByteArray × Bool) := #[]
    for _ in [0:32] do
      let (p, s') := s.next 1200 credit
      s := s'
      match p with
      | some p => batch := batch.push p
      | none => break
    if s.sentOffset > credit then ok := false
    for i in [0:batch.size] do
      let (j, g') := g.next (batch.size - i); g := g'
      batch := batch.swapIfInBounds i (i + j)
    let mut acks := lateAcks
    let mut losses : Array (Nat × Nat × Bool) := #[]
    lateAcks := #[]
    for (o, d, f) in batch do
      let (x, g') := g.next 100; g := g'
      if x < 10 then
        losses := losses.push (o, d.size, f)
      else
        match r.insert o d f with
        | .ok r' => r := r'
        | .error _ => ok := false
        if x < 15 then
          match r.insert o d f with
          | .ok r' => r := r'
          | .error _ => ok := false
        if x < 20 then
          losses := losses.push (o, d.size, f)
          if x < 18 then lateAcks := lateAcks.push (o, d.size, f)
        else acks := acks.push (o, d.size, f)
    for (o, n, f) in acks do s := s.onAcked o n f
    for (o, n, f) in losses do s := s.onLost o n f
    let (m, g') := g.next 40000; g := g'
    let (r', b) := r.read m
    r := r'
    out := out ++ b
    if let some win := window then
      r := r.setLimit (r.readOffset + win)
    credit := r.limit
    maxBuf := max maxBuf s.buf.size
  let (r', b) := r.read total
  out := out ++ b
  r := r'
  let tag := s!"sim seed {seed} window {window}"
  check s!"{tag}: no errors" ok
  check s!"{tag}: completed ({rounds} rounds)" (s.isAllAcked && r.isFinished)
  check s!"{tag}: data" (out.size == total && out == src)
  check s!"{tag}: nothing buffered" (s.buffered == 0 && s.buf.size < 8192)
  check s!"{tag}: final size" (r.finalSize == some total && s.writtenOffset == total)
  IO.println s!"{tag}: {rounds} rounds, peak send buffer {maxBuf}"

end LeanQUIC.Tests.Buffers

open LeanQUIC.Tests.Buffers in
def main : IO UInt32 := do
  let fails ← IO.mkRef 0
  let total ← IO.mkRef 0
  let chk (name : String) (ok : Bool) : IO Unit := do
    total.modify (· + 1)
    check fails name ok
  recvTests chk
  sendTests chk
  let t0 ← IO.monoMsNow
  simulate chk 1 none
  let t1 ← IO.monoMsNow
  IO.println s!"3 MB lossy simulation: {t1 - t0} ms"
  simulate chk 42 none
  simulate chk 3 (some 65536)
  let t2 ← IO.monoMsNow
  simulate chk 9 (some 4000)
  let t3 ← IO.monoMsNow
  IO.println s!"3 MB flow-controlled (4000-byte window) simulation: {t3 - t2} ms"
  let f ← fails.get
  let n ← total.get
  IO.println s!"{n - f}/{n} checks passed"
  return if f == 0 then 0 else 1
