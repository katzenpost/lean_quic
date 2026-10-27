/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import LeanQUICBench.Packet
import LeanQUICBench.Frame
import LeanQUICBench.Buffers
import LeanQUICBench.Conn

/-! # Benchmark driver -/

def main (args : List String) : IO UInt32 := do
  (← LeanQUICBench.Packet.benches).forM LeanBench.register
  (← LeanQUICBench.Frame.benches).forM LeanBench.register
  (← LeanQUICBench.Buffers.benches).forM LeanBench.register
  (← LeanQUICBench.Conn.benches).forM LeanBench.register
  LeanBench.runMain args
