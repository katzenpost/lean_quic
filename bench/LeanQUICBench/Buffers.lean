/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import LeanQUIC
import LeanBench
import LeanQUICBench.Packet

/-! # Stream buffers at growing sizes

The send side: a write, then taking it out in packet-sized chunks; and the same data written 1 KiB
at a time. The receive side: packet-sized chunks inserted in order with a read after each, and
inserted with each pair swapped so every other chunk waits out of order. -/

namespace LeanQUICBench.Buffers

open LeanQUIC.Buffers
open LeanQUICBench.Packet (cfg bytes)

def sizes : List (Nat × String) :=
  [(16384, "16KiB"), (65536, "64KiB"), (262144, "256KiB"), (1048576, "1MiB")]

/-- Stream data per packet. -/
def chunk : Nat := 1150

/-- Write `data` and take it out in packet-sized chunks; the bytes taken. -/
def sendAll (data : ByteArray) : Nat := Id.run do
  let mut s := Send.init.write data
  let mut n := 0
  for _ in [0:data.size / chunk + 2] do
    let (c, s') := s.next chunk (2 ^ 62)
    s := s'
    match c with
    | some (_, d, _) => n := n + d.size
    | none => break
  pure n

/-- Write `data` in `piece`-byte writes; the bytes written. -/
def writePieces (piece data : ByteArray) : Nat := Id.run do
  let mut s := Send.init
  for _ in [0:data.size / piece.size] do
    s := s.write piece
  pure s.writtenOffset

/-- Insert the chunks in this order, reading what becomes contiguous after each; the bytes read. -/
def recvAll (chunks : Array (Nat × ByteArray)) : Nat := Id.run do
  let mut r := Recv.init (2 ^ 62)
  let mut n := 0
  for (off, d) in chunks do
    match r.insert off d false with
    | .ok r' =>
      let (r', out) := r'.read r'.readable
      r := r'
      n := n + out.size
    | .error _ => return 0
  pure n

def chunksOf (data : ByteArray) : Array (Nat × ByteArray) :=
  (Array.range ((data.size + chunk - 1) / chunk)).map fun i =>
    (i * chunk, data.extract (i * chunk) (i * chunk + chunk))

/-- Each pair of neighbouring chunks swapped. -/
def swapPairs (cs : Array (Nat × ByteArray)) : Array (Nat × ByteArray) := Id.run do
  let mut out := #[]
  for i in [0:cs.size / 2] do
    out := (out.push cs[2 * i + 1]!).push cs[2 * i]!
  if cs.size % 2 == 1 then out := out.push cs.back!
  pure out

def benches : IO (Array LeanBench.Bench) := do
  let out ← IO.mkRef 0
  let piece ← IO.mkRef (bytes 1024)
  let mut bs := #[]
  for (size, label) in sizes do
    let data ← IO.mkRef (bytes size)
    let inOrder ← IO.mkRef (chunksOf (← data.get))
    let swapped ← IO.mkRef (swapPairs (← inOrder.get))
    for (name, n) in [("send all", sendAll (← data.get)), ("send 1KiB writes", writePieces (← piece.get) (← data.get)),
        ("recv in order", recvAll (← inOrder.get)), ("recv pairs swapped", recvAll (← swapped.get))] do
      unless n == size do throw (IO.userError s!"{name} {label}: {n} bytes")
    bs := bs.push { name := s!"stream send: write {label}, take 1150B chunks", config := cfg,
                    action := do out.set (sendAll (← data.get)) }
    bs := bs.push { name := s!"stream send: {label} in 1KiB writes", config := cfg,
                    action := do out.set (writePieces (← piece.get) (← data.get)) }
    bs := bs.push { name := s!"stream recv: {label} in order, read each", config := cfg,
                    action := do out.set (recvAll (← inOrder.get)) }
    bs := bs.push { name := s!"stream recv: {label} pairs swapped, read each", config := cfg,
                    action := do out.set (recvAll (← swapped.get)) }
  pure bs

end LeanQUICBench.Buffers
