/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

/-!
# Stream buffers

Receive reassembly and send retransmission buffers for QUIC STREAM and CRYPTO frames
(RFC 9000 §2–4, §19.6), with per-stream flow control limits.
-/

namespace LeanQUIC.Buffers

/-! ## Interval sets -/

/-- Half-open intervals that are non-empty, sorted, disjoint and non-adjacent. -/
def Valid (l : List (Nat × Nat)) : Prop :=
  l.Pairwise (fun x y => x.2 < y.1) ∧ ∀ x ∈ l, x.1 < x.2

/-- Union with `[lo, hi)`. -/
def ins (lo hi : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [(lo, hi)]
  | (a, b) :: t =>
    if hi < a then (lo, hi) :: (a, b) :: t
    else if b < lo then (a, b) :: ins lo hi t
    else ins (min a lo) (max b hi) t

/-- Difference with `[lo, hi)`. -/
def rem (lo hi : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | (a, b) :: t =>
    if hi ≤ a then (a, b) :: t
    else if b ≤ lo then (a, b) :: rem lo hi t
    else (if a < lo then [(a, lo)] else []) ++ (if hi < b then [(hi, b)] else []) ++ rem lo hi t

/-- The parts of `[lo, hi)` not covered by the list. -/
def gaps (lo hi : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => if lo < hi then [(lo, hi)] else []
  | (a, b) :: t =>
    if hi ≤ a then (if lo < hi then [(lo, hi)] else [])
    else if b ≤ lo then gaps lo hi t
    else (if lo < a then [(lo, a)] else []) ++ gaps (max lo b) hi t

theorem ins_lower {m lo hi : Nat} {l : List (Nat × Nat)} (hm : m < lo)
    (hl : ∀ y ∈ l, m < y.1) : ∀ x ∈ ins lo hi l, m < x.1 := by
  induction l generalizing lo hi with
  | nil => simp [ins]; omega
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    have ha : m < a := hl (a, b) (by simp)
    have ht : ∀ y ∈ t, m < y.1 := fun y hy => hl y (by simp [hy])
    simp only [ins]
    split
    · intro x hx
      simp at hx
      rcases hx with rfl | rfl | hx
      · exact hm
      · exact ha
      · exact ht _ hx
    · split
      · intro x hx
        simp at hx
        rcases hx with rfl | hx
        · exact ha
        · exact ih hm ht x hx
      · exact ih (by omega) ht

theorem ins_upper {m lo hi : Nat} {l : List (Nat × Nat)}
    (hl : ∀ y ∈ l, y.2 ≤ m) : ∀ x ∈ ins lo hi l, x.2 ≤ max m hi := by
  induction l generalizing lo hi with
  | nil => simp [ins]; omega
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    have hb : b ≤ m := hl (a, b) (by simp)
    have ht : ∀ y ∈ t, y.2 ≤ m := fun y hy => hl y (by simp [hy])
    simp only [ins]
    split
    · intro x hx
      simp at hx
      rcases hx with rfl | rfl | hx
      · omega
      · simp; omega
      · have := ht _ hx; omega
    · split
      · intro x hx
        simp at hx
        rcases hx with rfl | hx
        · simp; omega
        · exact ih ht x hx
      · intro x hx
        have := ih (lo := min a lo) (hi := max b hi) ht x hx
        omega

theorem ins_valid {lo hi : Nat} {l : List (Nat × Nat)} (h : lo < hi) (hv : Valid l) :
    Valid (ins lo hi l) := by
  induction l generalizing lo hi with
  | nil => simp [ins, Valid, h]
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    obtain ⟨hp, hpos⟩ := hv
    simp only [List.pairwise_cons] at hp
    have hab : a < b := hpos (a, b) (by simp)
    have hvt : Valid t := ⟨hp.2, fun x hx => hpos x (by simp [hx])⟩
    simp only [ins]
    split
    · refine ⟨?_, ?_⟩
      · simp only [List.pairwise_cons, List.mem_cons]
        refine ⟨?_, hp.1, hp.2⟩
        intro y hy
        rcases hy with rfl | hy
        · assumption
        · have := hp.1 y hy; omega
      · intro x hx
        simp at hx
        rcases hx with rfl | rfl | hx
        · exact h
        · exact hab
        · exact hvt.2 x hx
    · split
      · have ih' := ih h hvt
        refine ⟨?_, ?_⟩
        · simp only [List.pairwise_cons]
          exact ⟨ins_lower (by omega) hp.1, ih'.1⟩
        · intro x hx
          simp at hx
          rcases hx with rfl | hx
          · exact hab
          · exact ih'.2 x hx
      · exact ih (by omega) hvt

theorem rem_sub {lo hi : Nat} {l : List (Nat × Nat)} (hv : Valid l) :
    ∀ x ∈ rem lo hi l, x.1 < x.2 ∧ ∃ y ∈ l, y.1 ≤ x.1 ∧ x.2 ≤ y.2 := by
  induction l with
  | nil => simp [rem]
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    have hab : a < b := hv.2 (a, b) (by simp)
    have hvt : Valid t := ⟨(List.pairwise_cons.1 hv.1).2, fun x hx => hv.2 x (by simp [hx])⟩
    have ih := ih hvt
    simp only [rem]
    intro x hx
    split at hx
    · exact ⟨hv.2 x hx, x, hx, Nat.le_refl _, Nat.le_refl _⟩
    · split at hx
      · simp at hx
        rcases hx with rfl | hx
        · exact ⟨hab, (a, b), by simp, Nat.le_refl _, Nat.le_refl _⟩
        · obtain ⟨h1, y, hy, h2⟩ := ih x hx
          exact ⟨h1, y, by simp [hy], h2⟩
      · simp only [List.mem_append] at hx
        rcases hx with (hx | hx) | hx
        · split at hx
          · simp at hx; subst hx
            exact ⟨by assumption, (a, b), by simp, by simp, by simp; omega⟩
          · simp at hx
        · split at hx
          · simp at hx; subst hx
            refine ⟨by assumption, (a, b), by simp, by simp; omega, by simp⟩
          · simp at hx
        · obtain ⟨h1, y, hy, h2⟩ := ih x hx
          exact ⟨h1, y, by simp [hy], h2⟩

theorem rem_valid {lo hi : Nat} {l : List (Nat × Nat)} (h : lo < hi) (hv : Valid l) :
    Valid (rem lo hi l) := by
  induction l with
  | nil => simp [rem, Valid]
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    have hp := List.pairwise_cons.1 hv.1
    have hab : a < b := hv.2 (a, b) (by simp)
    have hvt : Valid t := ⟨hp.2, fun x hx => hv.2 x (by simp [hx])⟩
    have ih := ih hvt
    have sub := rem_sub (lo := lo) (hi := hi) hvt
    have after : ∀ x ∈ rem lo hi t, b < x.1 := fun x hx => by
      obtain ⟨_, y, hy, h2, _⟩ := sub x hx
      have := hp.1 y hy; omega
    refine ⟨?_, fun x hx => (rem_sub hv x hx).1⟩
    simp only [rem]
    split
    · exact hv.1
    · split
      · exact List.pairwise_cons.2 ⟨after, ih.1⟩
      · simp only [List.pairwise_append]
        refine ⟨⟨?_, ?_, ?_⟩, ih.1, ?_⟩
        · split <;> simp
        · split <;> simp
        · split <;> split <;> simp <;> omega
        · intro x hx y hy
          have := after y hy
          simp only [List.mem_append] at hx
          rcases hx with hx | hx <;> (split at hx <;> simp at hx) <;> subst hx <;> simp <;> omega

/-- A finite union of half-open intervals, with an upper bound on every end. -/
structure RangeSet where
  ranges : Array (Nat × Nat) := #[]
  bound : Nat := 0
  valid : Valid ranges.toList := by simp [Valid]
  bounded : ∀ x ∈ ranges.toList, x.2 ≤ bound := by simp

namespace RangeSet

/-- The empty set. -/
def empty : RangeSet := {}

theorem append_valid {l : List (Nat × Nat)} {lo hi m : Nat} (hv : Valid l)
    (hb : ∀ x ∈ l, x.2 ≤ m) (hm : m < lo) (h : lo < hi) : Valid (l ++ [(lo, hi)]) := by
  refine ⟨?_, ?_⟩
  · simp only [List.pairwise_append]
    refine ⟨hv.1, by simp, ?_⟩
    intro x hx y hy
    simp at hy; subst hy
    have := hb x hx; simp; omega
  · intro x hx
    simp at hx
    rcases hx with hx | rfl
    · exact hv.2 x hx
    · exact h

/-- Add `[lo, hi)`; appending past the bound is O(1). -/
def insert (s : RangeSet) (lo hi : Nat) : RangeSet :=
  if h : lo < hi then
    if hm : s.ranges.isEmpty ∨ s.bound < lo then
      { ranges := s.ranges.push (lo, hi), bound := hi
        valid := by
          rcases hm with hm | hm
          · have : s.ranges.toList = [] := by simpa [Array.isEmpty_iff] using hm
            simp [this, Valid, h]
          · simpa using append_valid s.valid s.bounded hm h
        bounded := by
          intro x hx
          simp at hx
          rcases hx with hx | rfl
          · rcases hm with hm | hm
            · simp [Array.isEmpty_iff] at hm
              simp [hm] at hx
            · have := s.bounded x (by simpa using hx); omega
          · simp }
    else
      { ranges := (ins lo hi s.ranges.toList).toArray, bound := max s.bound hi
        valid := by simpa using ins_valid h s.valid
        bounded := by simpa using ins_upper s.bounded }
  else s

/-- Remove `[lo, hi)`. -/
def erase (s : RangeSet) (lo hi : Nat) : RangeSet :=
  if h : lo < hi then
    { ranges := (rem lo hi s.ranges.toList).toArray, bound := s.bound
      valid := by simpa using rem_valid h s.valid
      bounded := by
        intro x hx
        obtain ⟨_, y, hy, _, h2⟩ := rem_sub s.valid x (by simpa using hx)
        have := s.bounded y hy; omega }
  else s

/-- The lowest interval, if any. -/
def first? (s : RangeSet) : Option (Nat × Nat) := s.ranges[0]?

/-- The parts of `[lo, hi)` not in the set. -/
def missing (s : RangeSet) (lo hi : Nat) : List (Nat × Nat) := gaps lo hi s.ranges.toList

/-- No intervals. -/
def isEmpty (s : RangeSet) : Bool := s.ranges.isEmpty

end RangeSet


/-! ## Errors -/

/-- Stream receive errors, each mapping to a QUIC transport error code. -/
inductive Error where
  /-- Data beyond the receive limit (FLOW_CONTROL_ERROR). -/
  | flowControl
  /-- Final size changed or data beyond it (FINAL_SIZE_ERROR). -/
  | finalSize
  /-- CRYPTO data beyond the reassembly cap (CRYPTO_BUFFER_EXCEEDED). -/
  | bufferExceeded
deriving DecidableEq, Repr, Inhabited

/-! ## Receive side -/

/-- A received slice `data[lo, hi)` placed at stream offset `off`. -/
structure Seg where
  off : Nat
  data : ByteArray
  lo : Nat
  hi : Nat
deriving Inhabited

/-- Length of a segment. -/
def Seg.len (g : Seg) : Nat := g.hi - g.lo

/-- Stream offset one past the segment. -/
def Seg.stop (g : Seg) : Nat := g.off + g.len

/-- Index of the first segment ending after `x` (segments sorted and disjoint). -/
def firstStopAfter (segs : Array Seg) (x : Nat) : Nat := go 0 segs.size
where
  go (lo hi : Nat) : Nat :=
    if lo < hi then
      let mid := (lo + hi) / 2
      if segs[mid]!.stop > x then go lo mid else go (mid + 1) hi
    else lo
  termination_by hi - lo

/-- Merge a segment into a sorted disjoint array, keeping only the parts not yet present. -/
def placeSeg (segs : Array Seg) (g : Seg) : Array Seg :=
  if segs.isEmpty || segs.back!.stop ≤ g.off then segs.push g
  else Id.run do
    let e := g.stop
    let i := firstStopAfter segs g.off
    let mut acc := segs.extract 0 i
    let mut c := g.off
    let mut j := i
    for k in [i:segs.size] do
      let x := segs[k]!
      if x.off ≥ e then break
      if c < x.off then
        acc := acc.push { g with off := c, lo := g.lo + (c - g.off), hi := g.lo + (x.off - g.off) }
      acc := acc.push x
      c := max c x.stop
      j := k + 1
    if c < e then
      acc := acc.push { g with off := c, lo := g.lo + (c - g.off) }
    return acc ++ segs.extract j segs.size

/-- Move segments contiguous with the end of `ready` (at stream offset `base`) into it. -/
def drain (base : Nat) (ready : ByteArray) (segs : Array Seg) : ByteArray × Array Seg := Id.run do
  let mut ready := ready
  let mut n := 0
  for g in segs do
    let cend := base + ready.size
    if g.off > cend then break
    let skip := cend - g.off
    if skip < g.len then
      ready := g.data.copySlice (g.lo + skip) ready ready.size (g.len - skip) false
    n := n + 1
  return if n == 0 then (ready, segs) else (ready, segs.extract n segs.size)

/-- Receive side: reassembles out-of-order, overlapping, duplicated ranges. -/
structure Recv where
  /-- Contiguous bytes starting at stream offset `base`; `ready[pos:]` is unread. -/
  ready : ByteArray
  pos : Nat
  base : Nat
  /-- Out-of-order data past the end of `ready`, sorted and disjoint. -/
  segs : Array Seg
  lim : Nat
  fin : Option Nat
  high : Nat
  crypto : Bool

/-- A receive buffer accepting data up to offset `limit` (exclusive). -/
def Recv.init (limit : Nat) : Recv :=
  { ready := .empty, pos := 0, base := 0, segs := #[], lim := limit, fin := none, high := 0,
    crypto := false }

/-- A CRYPTO receive buffer: data past `cap` is `bufferExceeded` instead of `flowControl`. -/
def Recv.initCrypto (cap : Nat) : Recv := { Recv.init cap with crypto := true }

/-- Accept `data` at `offset`, with `fin` marking its end as the final size. -/
def Recv.insert (r : Recv) (offset : Nat) (data : ByteArray) (fin : Bool) : Except Error Recv :=
  let stop := offset + data.size
  if stop > r.lim then .error (if r.crypto then .bufferExceeded else .flowControl)
  else if (match r.fin with
      | some f => decide (stop > f) || (fin && stop != f)
      | none => fin && decide (stop < r.high)) then .error .finalSize
  else
    match r with
    | ⟨ready, pos, base, segs, lim, f, high, crypto⟩ =>
      let f := if fin then some stop else f
      let high := max high stop
      let cend := base + ready.size
      let s := max offset cend
      if stop ≤ s then .ok ⟨ready, pos, base, segs, lim, f, high, crypto⟩
      else if segs.isEmpty && s == cend then
        let ready := data.copySlice (s - offset) ready ready.size (stop - s) false
        .ok ⟨ready, pos, base, segs, lim, f, high, crypto⟩
      else
        let (ready, segs) := drain base ready (placeSeg segs ⟨s, data, s - offset, data.size⟩)
        .ok ⟨ready, pos, base, segs, lim, f, high, crypto⟩

/-- Contiguous bytes available now. -/
def Recv.readable (r : Recv) : Nat := r.ready.size - r.pos

/-- Stream offset of the next byte to read. -/
def Recv.readOffset (r : Recv) : Nat := r.base + r.pos

/-- Contiguous bytes from the read offset, at most `max`; consumes them. -/
def Recv.read (r : Recv) (max : Nat) : Recv × ByteArray :=
  let k := min max (r.ready.size - r.pos)
  let out := r.ready.extract r.pos (r.pos + k)
  let pos := r.pos + k
  if pos ≥ r.ready.size then ({ r with ready := .empty, pos := 0, base := r.base + pos }, out)
  else if 4096 ≤ pos ∧ r.ready.size ≤ 2 * pos then
    ({ r with ready := r.ready.extract pos r.ready.size, pos := 0, base := r.base + pos }, out)
  else ({ r with pos }, out)

/-- The final size, once a FIN has been received. -/
def Recv.finalSize (r : Recv) : Option Nat := r.fin

/-- FIN received and every byte up to it has been read. -/
def Recv.isFinished (r : Recv) : Bool :=
  match r.fin with
  | some f => r.readOffset == f
  | none => false

/-- Highest offset (exclusive) the peer may send to. -/
def Recv.limit (r : Recv) : Nat := r.lim

/-- Raise the limit; decreases are ignored. -/
def Recv.setLimit (r : Recv) (limit : Nat) : Recv := { r with lim := max r.lim limit }

/-- Highest offset received so far (for connection-level flow control accounting). -/
def Recv.highestOffset (r : Recv) : Nat := r.high

theorem Recv.read_size_le (r : Recv) (n : Nat) : (r.read n).2.size ≤ n := by
  simp only [Recv.read]
  split <;> (try split) <;> simp <;> omega

theorem Recv.readable_read (r : Recv) (n : Nat) :
    (r.read n).1.readable = r.readable - (r.read n).2.size := by
  simp only [Recv.read, Recv.readable]
  split
  · simp; omega
  · split <;> simp <;> omega

theorem Recv.readOffset_read (r : Recv) (n : Nat) :
    (r.read n).1.readOffset = r.readOffset + (r.read n).2.size := by
  simp only [Recv.read, Recv.readOffset]
  split
  · simp; omega
  · split <;> simp <;> omega

theorem Recv.read_size_eq (r : Recv) (n : Nat) : (r.read n).2.size = min n r.readable := by
  simp only [Recv.read, Recv.readable]
  split <;> (try split) <;> simp <;> omega

theorem Recv.limit_setLimit (r : Recv) (l : Nat) : (r.setLimit l).limit = max r.limit l := rfl

theorem Recv.insert_flowControl (r : Recv) (offset : Nat) (data : ByteArray) (fin : Bool)
    (h : offset + data.size > r.limit) (hc : r.crypto = false) :
    r.insert offset data fin = .error .flowControl := by
  simp [Recv.insert, Recv.limit] at *
  simp [h, hc]

/-! ## Send side -/

/-- Send side: data written by the application, sent in chunks, retransmitted when lost. -/
structure Send where
  /-- Written bytes from stream offset `bufOff` on. -/
  buf : ByteArray
  bufOff : Nat
  /-- Every byte below `ackedTo` is acked. -/
  ackedTo : Nat
  /-- Acked ranges above `ackedTo`. -/
  acked : RangeSet
  /-- Sent, lost and not acked ranges awaiting retransmission. -/
  lost : RangeSet
  written : Nat
  sent : Nat
  finished : Bool
  finSent : Bool
  finLost : Bool
  finAcked : Bool

/-- An empty, open send buffer. -/
def Send.init : Send :=
  { buf := .empty, bufOff := 0, ackedTo := 0, acked := {}, lost := {}, written := 0, sent := 0,
    finished := false, finSent := false, finLost := false, finAcked := false }

/-- Append application data; ignored after `finish`. -/
def Send.write (s : Send) (data : ByteArray) : Send :=
  if s.finished then s
  else
    let buf := s.buf
    let s := { s with buf := .empty }
    { s with buf := buf ++ data, written := s.written + data.size }

/-- No more writes; FIN goes with the last byte (or alone if all already sent). -/
def Send.finish (s : Send) : Send := { s with finished := true }

/-- The FIN still has to be (re)transmitted. -/
def Send.finDue (s : Send) : Bool := s.finished && !s.finAcked && (!s.finSent || s.finLost)

/-- The next chunk to send: lost ranges first (lowest offset first), then new data up to `limit`.
At most `maxLen` bytes; a FIN-only chunk (empty data, fin) is possible. -/
def Send.next (s : Send) (maxLen : Nat) (limit : Nat) : Option (Nat × ByteArray × Bool) × Send :=
  match s.lost.first? with
  | some (a, b) =>
    if maxLen = 0 then (none, s)
    else
      let n := min (b - a) maxLen
      let data := s.buf.extract (a - s.bufOff) (a + n - s.bufOff)
      let fin := s.finDue && a + n == s.written
      (some (a, data, fin),
        { s with lost := s.lost.erase a (a + n), finSent := s.finSent || fin,
                 finLost := s.finLost && !fin })
  | none =>
    let a := s.sent
    let n := min maxLen (min (s.written - a) (limit - a))
    if n > 0 then
      let data := s.buf.extract (a - s.bufOff) (a + n - s.bufOff)
      let fin := s.finDue && a + n == s.written
      (some (a, data, fin),
        { s with sent := a + n, finSent := s.finSent || fin, finLost := s.finLost && !fin })
    else if s.finDue && a == s.written then
      (some (a, .empty, true), { s with finSent := true, finLost := false })
    else (none, s)

/-- Drop buffered bytes below `ackedTo` once they are at least half the buffer. -/
def Send.compact (s : Send) : Send :=
  let dead := s.ackedTo - s.bufOff
  if 4096 ≤ dead ∧ s.buf.size ≤ 2 * dead then
    { s with buf := s.buf.extract dead s.buf.size, bufOff := s.ackedTo }
  else s

/-- Record an acknowledgement of `[offset, offset + len)` and possibly the FIN. -/
def Send.onAcked (s : Send) (offset len : Nat) (fin : Bool) : Send :=
  let s := if fin && s.finSent then { s with finAcked := true, finLost := false } else s
  let lo := max offset s.ackedTo
  let hi := min (offset + len) s.sent
  if lo < hi then
    let acked := s.acked.insert lo hi
    let lost := s.lost.erase lo hi
    let (ackedTo, acked) := match acked.first? with
      | some (a, b) => if a ≤ s.ackedTo then (b, acked.erase a b) else (s.ackedTo, acked)
      | none => (s.ackedTo, acked)
    Send.compact { s with acked, lost, ackedTo }
  else s

/-- Requeue whatever of `[offset, offset + len)` (and the FIN) is not yet acked. -/
def Send.onLost (s : Send) (offset len : Nat) (fin : Bool) : Send :=
  let lo := max offset s.ackedTo
  let hi := min (offset + len) s.sent
  let lost := (s.acked.missing lo hi).foldl (fun l (a, b) => l.insert a b) s.lost
  { s with lost, finLost := s.finLost || (fin && s.finSent && !s.finAcked) }

/-- Something is sendable, ignoring flow control. -/
def Send.hasPending (s : Send) : Bool := !s.lost.isEmpty || s.sent < s.written || s.finDue

/-- Finished, and every byte and the FIN acked. -/
def Send.isAllAcked (s : Send) : Bool := s.finished && s.finAcked && s.ackedTo == s.written

/-- Total bytes written. -/
def Send.writtenOffset (s : Send) : Nat := s.written

/-- Highest offset ever sent (for flow control accounting). -/
def Send.sentOffset (s : Send) : Nat := s.sent

/-- Bytes kept for retransmission: written past the contiguously acked prefix. -/
def Send.buffered (s : Send) : Nat := s.written - s.ackedTo

theorem Send.sentOffset_next_le (s : Send) (maxLen limit : Nat) :
    (s.next maxLen limit).2.sentOffset ≤ max s.sentOffset limit := by
  simp only [Send.next, Send.sentOffset]
  split
  · split <;> simp <;> omega
  · split
    · simp; omega
    · split <;> simp <;> omega

theorem Send.sentOffset_le_next (s : Send) (maxLen limit : Nat) :
    s.sentOffset ≤ (s.next maxLen limit).2.sentOffset := by
  simp only [Send.next, Send.sentOffset]
  split
  · split <;> simp
  · split
    · simp
    · split <;> simp

theorem Send.next_size_le (s : Send) (maxLen limit : Nat) {o : Nat} {d : ByteArray} {f : Bool}
    (h : (s.next maxLen limit).1 = some (o, d, f)) : d.size ≤ maxLen := by
  simp only [Send.next] at h
  split at h
  · split at h
    · simp at h
    · simp at h; obtain ⟨_, rfl, _⟩ := h; simp; omega
  · split at h
    · simp at h; obtain ⟨_, rfl, _⟩ := h; simp; omega
    · split at h
      · simp at h; obtain ⟨_, rfl, _⟩ := h; simp
      · simp at h

end LeanQUIC.Buffers
