/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import LeanQUIC.Packet

namespace LeanQUIC

/-! # The sending side of a packet number space

A `Sealer` holds a space's write keys and its next packet number, and is the only way to seal a
packet: `send` takes the packet number from the counter and hands it to `protect`, so callers
never choose one. Its constructor is private, and the counter only moves forward: `rekey` (a key
update, or new Initial keys after a Retry) and `discard` keep it, `send` increments it, and
sealing stops at `2^62` (RFC 9000 §12.3).

The law, `run_nonces_nodup`: along any sequence of these steps the sealed packet numbers strictly
increase, so no two packets of the space are sealed under the same nonce, whatever the keys were
at the time. Spaces have separate sealers; that their keys differ is HKDF's to make true (the
secrets come from different labels or handshake stages), not something proved here. -/

/-- One past the largest packet number (RFC 9000 §12.3). -/
def pnLimit : Nat := 2 ^ 62

structure Sealer where
  private mk ::
  keys : Option Keys
  nextPn : Nat
  bound : nextPn ≤ pnLimit

namespace Sealer

instance : Inhabited Sealer := ⟨⟨none, 0, by decide⟩⟩

def init : Sealer := default

/-- New keys, the packet number unchanged. -/
def rekey (s : Sealer) (k : Keys) : Sealer := ⟨some k, s.nextPn, s.bound⟩

def discard (s : Sealer) : Sealer := ⟨none, s.nextPn, s.bound⟩

/-- Seal the packet `build` makes for the next packet number: its header (ending with the packet
number), packet number length and payload. `none` without keys or packet numbers. -/
def send (s : Sealer) (long : Bool) (build : Nat → ByteArray × Nat × ByteArray) :
    Option (Sealer × Nat × ByteArray) :=
  match s.keys with
  | none => none
  | some k =>
    if h : s.nextPn < pnLimit then
      let pn := s.nextPn
      let (hdr, pnLen, payload) := build pn
      some (⟨s.keys, pn + 1, h⟩, pn, protect k long hdr pn pnLen payload)
    else none

theorem send_pn {s s' : Sealer} {long build pn pkt} (h : s.send long build = some (s', pn, pkt)) :
    pn = s.nextPn ∧ s'.nextPn = pn + 1 ∧ s'.keys = s.keys := by
  unfold send at h
  split at h
  · contradiction
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact ⟨rfl, rfl, rfl⟩
    · contradiction

/-- The packet is sealed by `protect` with the sealer's keys and the packet number it reports. -/
theorem send_packet {s s' : Sealer} {long build pn pkt} (h : s.send long build = some (s', pn, pkt)) :
    ∃ k, s.keys = some k ∧ pkt = protect k long (build pn).1 pn (build pn).2.1 (build pn).2.2 := by
  unfold send at h
  split at h
  · contradiction
  · rename_i k hk
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      exact ⟨k, hk, rfl⟩
    · contradiction

theorem pn_lt {s s' : Sealer} {long build pn pkt} (h : s.send long build = some (s', pn, pkt)) :
    pn < pnLimit := by
  have := (send_pn h).2.1 ▸ s'.bound
  omega

/-- What can happen to a sealer. -/
inductive Step where
  | rekey (k : Keys)
  | discard
  | send (long : Bool) (build : Nat → ByteArray × Nat × ByteArray)

/-- Run steps, collecting the packet numbers of the packets sealed. -/
def run : Sealer → List Step → Sealer × List Nat
  | s, [] => (s, [])
  | s, .rekey k :: rest => run (s.rekey k) rest
  | s, .discard :: rest => run s.discard rest
  | s, .send long build :: rest =>
    match s.send long build with
    | some (s', pn, _) => let (t, pns) := run s' rest; (t, pn :: pns)
    | none => run s rest

/-- Sealed packet numbers lie between the starting and the final counter, strictly increasing. -/
theorem run_sorted : ∀ (steps : List Step) (s : Sealer),
    (∀ pn ∈ (s.run steps).2, s.nextPn ≤ pn ∧ pn < (s.run steps).1.nextPn ∧ pn < pnLimit) ∧
    (s.run steps).2.Pairwise (· < ·) ∧ s.nextPn ≤ (s.run steps).1.nextPn
  | [], s => by simp [run]
  | .rekey k :: rest, s => by simpa [run, rekey] using run_sorted rest (s.rekey k)
  | .discard :: rest, s => by simpa [run, discard] using run_sorted rest s.discard
  | .send long build :: rest, s => by
    simp only [run]
    split
    · rename_i s' pn pkt h
      obtain ⟨hpn, hnext, -⟩ := send_pn h
      have hlt := pn_lt h
      obtain ⟨hall, hpair, hle⟩ := run_sorted rest s'
      dsimp only
      refine ⟨?_, ?_, by omega⟩
      · intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact ⟨by omega, by omega, hlt⟩
        · have := hall q hq
          exact ⟨by omega, this.2⟩
      · refine List.Pairwise.cons (fun q hq => ?_) hpair
        have := hall q hq
        omega
    · exact run_sorted rest s

/-- No two packets sealed along a run share a nonce under the same IV. -/
theorem run_nonces_nodup (steps : List Step) (s : Sealer) (iv : Vector UInt8 12) :
    ((s.run steps).2.map (nonce iv)).Nodup := by
  obtain ⟨hall, hpair, -⟩ := run_sorted steps s
  rw [List.Nodup, List.pairwise_map]
  refine hpair.imp_of_mem fun ha hb hlt hn => ?_
  have := nonce_injective iv (Nat.lt_trans (hall _ ha).2.2 (by decide))
    (Nat.lt_trans (hall _ hb).2.2 (by decide)) hn
  omega

end Sealer

end LeanQUIC
