/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import LeanQUIC
import LeanBench
import LeanQUICBench.Packet

/-! # Frame encoding and parsing: ACK frames with growing numbers of ranges, and a STREAM frame
filling a 1200-byte packet -/

namespace LeanQUICBench.Frame

open LeanQUIC
open LeanQUICBench.Packet (cfg bytes)

/-- `n` two-packet ranges, largest first, one packet missing between neighbours. -/
def ranges (n : Nat) : List (Nat × Nat) :=
  (List.range n).map fun i => (100000 - 4 * i - 1, 100000 - 4 * i)

def benches : IO (Array LeanBench.Bench) := do
  let out ← IO.mkRef ByteArray.empty
  let parsed ← IO.mkRef (none : Option (Array LeanQUIC.Frame))
  let rs ← IO.mkRef ([] : List (Nat × Nat))
  let mut bs := #[]
  for n in [1, 4, 16, 64] do
    let f ← IO.mkRef (LeanQUIC.Frame.ack (ranges n) 3)
    let enc ← IO.mkRef (LeanQUIC.Frame.encode (← f.get))
    unless (LeanQUIC.Frame.parseAll (← enc.get)).isSome do throw (IO.userError "ACK does not parse")
    bs := bs.push { name := s!"ACK encode {n} ranges", config := cfg,
                    action := do out.set (LeanQUIC.Frame.encode (← f.get)) }
    bs := bs.push { name := s!"ACK parse {n} ranges", config := cfg,
                    action := do parsed.set (LeanQUIC.Frame.parseAll (← enc.get)) }
  let recvRanges ← IO.mkRef (ranges 32)
  let pn ← IO.mkRef 100001
  bs := bs.push { name := "addRange to 32 ranges", config := cfg,
                  action := do rs.set (LeanQUIC.addRange (← recvRanges.get) (← pn.get)) }
  -- The frames of a full 1-RTT packet: an ACK and as much stream data as fits.
  let data ← IO.mkRef (bytes 1150)
  let sf ← IO.mkRef (LeanQUIC.Frame.stream 0 65536 (← data.get) false)
  let payload ← IO.mkRef (LeanQUIC.Frame.encode (.ack (ranges 1) 3) ++ LeanQUIC.Frame.encode (← sf.get))
  bs := bs.push { name := "STREAM frame encode 1150B", config := cfg,
                  action := do out.set (LeanQUIC.Frame.encode (← sf.get)) }
  bs := bs.push { name := "parseAll ACK + STREAM 1150B payload", config := cfg,
                  action := do parsed.set (LeanQUIC.Frame.parseAll (← payload.get)) }
  pure bs

end LeanQUICBench.Frame
