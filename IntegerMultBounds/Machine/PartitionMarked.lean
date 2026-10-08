import IntegerMultBounds.Machine.Partition
import IntegerMultBounds.Machine.Protected
import IntegerMultBounds.Machine.Rewind

/-! A stable partition with a distinct left sentinel on every tape. The concrete
partition control only moves heads right or stays, so alphabet widening cannot
touch these markers. Whole-tape outputs support subsequent literal rewinds. -/

namespace IntegerMultBounds.Machine.PartitionMarked

private theorem emit_rightward (b : Bool) (next : Fin 3) (symbols : Fin 3 → Fin 4)
    (i : Fin 3) : 0 ≤ ((Partition.emit b next symbols).2 i).2.offset := by
  simp only [Partition.emit]
  split <;> simp [Move.offset]

/-- Inspect the actual transition table: no partition transition moves left. -/
theorem transition_rightward {s next : Fin 3} {symbols : Fin 3 → Fin 4}
    {action : Fin 3 → Fin 4 × Move}
    (h : Partition.program.transition s symbols = some (next, action))
    (i : Fin 3) : 0 ≤ (action i).2.offset := by
  dsimp only [Partition.program] at h
  split at h
  · split at h
    · cases h; exact emit_rightward _ 0 symbols i
    · split at h
      · cases h; exact emit_rightward _ 0 symbols i
      · contradiction
  · cases h; exact emit_rightward _ 0 symbols i

theorem step_head_mono {c d : Config 3 3 0}
    (h : step Partition.program c = some d) (i : Fin 3) : c.head i ≤ d.head i := by
  unfold step at h
  split at h
  · contradiction
  · rename_i next action ht
    have hmove := transition_rightward ht i
    simp only [Option.some.injEq] at h
    subst d
    dsimp
    omega

/-- All intermediate head positions stay at or to the right of their origins. -/
theorem run_head_mono {k : ℕ} {c d : Config 3 3 0}
    (h : run Partition.program k c = some d) (i : Fin 3) : c.head i ≤ d.head i := by
  induction k generalizing c with
  | zero => cases h; exact le_rfl
  | succ k ih =>
    obtain ⟨next, hs, hr⟩ := Option.bind_eq_some_iff.mp h
    exact (step_head_mono hs i).trans (ih hr)

def marker : Fin 5 := 4

def encoding : Alphabet.Encoding 0 1 := Alphabet.widen 0 1

def program : Program 3 3 1 := Alphabet.program encoding Partition.program

/-- A word at any integer origin, with a distinct marker immediately to its left
and blank cells everywhere else. -/
def markedTape (origin : ℤ) (xs : List (Fin 4)) (j : ℤ) : Fin 5 :=
  if j = origin - 1 then marker else encoding.encode (putWord (fun _ => blank) origin xs j)

@[simp] theorem markedTape_marker (origin : ℤ) (xs : List (Fin 4)) :
    markedTape origin xs (origin - 1) = marker := by simp [markedTape]

theorem encoding_ne_marker (x : Fin 4) : encoding.encode x ≠ marker := by
  intro h
  have hv := congrArg Fin.val h
  have hx := x.isLt
  change x.val = 4 at hv
  omega

theorem markedTape_ne_marker (origin : ℤ) (xs : List (Fin 4)) (j : ℤ)
    (h : j ≠ origin - 1) : markedTape origin xs j ≠ marker := by
  simp only [markedTape, h, ↓reduceIte]
  exact encoding_ne_marker _

private theorem putWord_map {a b : ℕ} (e : Alphabet.Encoding a b)
    (f : ℤ → Fin (a + 4)) (p : ℤ) (xs : List (Fin (a + 4))) :
    putWord (fun j => e.encode (f j)) p (xs.map e.encode) =
      fun j => e.encode (putWord f p xs j) := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, putWord, ih]
    funext j
    by_cases hj : j = p <;> simp [hj]

/-- The marked representation is exactly a word written over an empty marked
tape. This exposes the segment interface required by copying and concatenation. -/
theorem markedTape_putWord (origin : ℤ) (xs : List (Fin 4)) :
    markedTape origin xs = putWord (markedTape origin []) origin (xs.map encoding.encode) := by
  have hempty : markedTape origin [] =
      Function.update (fun _ => (blank : Fin 5)) (origin - 1) marker := by
    funext j
    simp [markedTape, putWord, Function.update_apply]
    rfl
  rw [hempty, putWord_update_before _ _ _ _ _ (by omega)]
  have hmap := putWord_map encoding (fun _ => (blank : Fin 4)) origin xs
  change putWord (fun _ => (blank : Fin 5)) origin (xs.map encoding.encode) = _ at hmap
  rw [hmap]
  funext j
  simp [markedTape, Function.update_apply]

theorem markedTape_end (origin : ℤ) (xs : List (Fin 4)) :
    markedTape origin xs (origin + xs.length) = blank := by
  have hm : origin + (xs.length : ℤ) ≠ origin - 1 := by omega
  simp only [markedTape, hm, ↓reduceIte]
  rw [putWord_outside _ _ _ _ (Or.inr le_rfl)]
  rfl

/-- Source, zero bucket, and one bucket in their physical tape order. -/
def cfg (p q r : ℤ) (xs ys zs : List (Fin 4)) (u v w : ℤ) : Config 3 3 1 where
  state := 0
  head := fun i => if i = 0 then u else if i = 1 then v else w
  tape := fun i => if i = 0 then markedTape p xs else if i = 1 then markedTape q ys
    else markedTape r zs

private def sourceCfg (p q r : ℤ) (xs ys zs : List (Fin 4)) (u v w : ℤ) : Config 3 3 0 :=
  Partition.cfg false (putWord (fun _ => blank) p xs)
    (putWord (fun _ => blank) q ys) (putWord (fun _ => blank) r zs) u v w 0

private def origins (p q r : ℤ) (i : Fin 3) : ℤ :=
  if i = 0 then p else if i = 1 then q else r

private def outside (p q r : ℤ) (i : Fin 3) (j : ℤ) : Fin 5 :=
  if j = origins p q r i - 1 then marker else blank

private theorem overlay_tape (origin : ℤ) (xs : List (Fin 4)) (j : ℤ) :
    (if origin ≤ j then encoding.encode (putWord (fun _ => blank) origin xs j)
      else if j = origin - 1 then marker else blank) = markedTape origin xs j := by
  by_cases h : origin ≤ j
  · have hm : j ≠ origin - 1 := by omega
    simp [h, markedTape, hm]
  · have hw := putWord_outside (fun _ => (blank : Fin 4)) origin j xs (Or.inl (by omega))
    simp [h, markedTape, hw, encoding]

private theorem overlay_cfg (p q r : ℤ) (xs ys zs : List (Fin 4)) (u v w : ℤ) :
    Alphabet.overlay encoding (fun i j => origins p q r i ≤ j) (outside p q r)
      (sourceCfg p q r xs ys zs u v w) = cfg p q r xs ys zs u v w := by
  classical
  unfold Alphabet.overlay sourceCfg Partition.cfg cfg
  congr 1
  funext i j
  fin_cases i <;> simp only [outside, origins, Partition.phase, Bool.false_eq_true,
    ↓reduceIte, Fin.zero_eta, Fin.isValue] <;> exact overlay_tape _ _ _

/-- A whole-tape, exact-time partition retaining three left sentinels. -/
theorem stream_exact (records : List Partition.Record) (p q r : ℤ) :
    run program (Partition.encode records).length
      (cfg p q r (Partition.encode records) [] [] p q r) =
      some (cfg p q r (Partition.encode records) (Partition.bucket false records)
        (Partition.bucket true records) (p + (Partition.encode records).length)
        (q + (Partition.bucket false records).length)
        (r + (Partition.bucket true records).length)) ∧
    step program (cfg p q r (Partition.encode records) (Partition.bucket false records)
      (Partition.bucket true records) (p + (Partition.encode records).length)
      (q + (Partition.bucket false records).length)
      (r + (Partition.bucket true records).length)) = none := by
  obtain ⟨hr, hh⟩ := Partition.stream_exact records (fun _ => blank)
    (fun _ => blank) (fun _ => blank) p q r rfl
  change run Partition.program (Partition.encode records).length
    (sourceCfg p q r (Partition.encode records) [] [] p q r) =
    some (sourceCfg p q r (Partition.encode records) (Partition.bucket false records)
      (Partition.bucket true records) (p + (Partition.encode records).length)
      (q + (Partition.bucket false records).length)
      (r + (Partition.bucket true records).length)) at hr
  have hregion : ∀ m z, m ≤ (Partition.encode records).length →
      run Partition.program m (sourceCfg p q r (Partition.encode records) [] [] p q r) =
        some z → ∀ i, origins p q r i ≤ z.head i := by
    intro m z _ hz i
    have hi := run_head_mono hz i
    simpa only [sourceCfg, Partition.cfg, origins, Partition.phase, Bool.false_eq_true,
      ↓reduceIte] using hi
  obtain ⟨hrun, hhalt, _⟩ := Alphabet.overlay_exact encoding Partition.program
    (fun i j => origins p q r i ≤ j) (outside p q r) hr hh hregion
  simpa only [overlay_cfg, program] using And.intro hrun hhalt

/-- The compositional specification retains every input and bucket cell. -/
theorem stream_hoare (records : List Partition.Record) (p q r : ℤ) :
    HoareTime program
      (fun v => v = (cfg p q r (Partition.encode records) [] [] p q r).tapes)
      (fun v => v = (cfg p q r (Partition.encode records) (Partition.bucket false records)
        (Partition.bucket true records) (p + (Partition.encode records).length)
        (q + (Partition.bucket false records).length)
        (r + (Partition.bucket true records).length)).tapes)
      (Partition.encode records).length := by
  rintro v rfl
  obtain ⟨hr, hh⟩ := stream_exact records p q r
  exact ⟨_, _, le_rfl, hr, hh, rfl⟩

/-- Any head at or beyond a marked word's origin rewinds to its left sentinel
in exactly distance-plus-one transitions, preserving all cells. -/
theorem rewind_exact (origin : ℤ) (xs : List (Fin 4)) (distance : ℕ) :
    run (Rewind.program marker) (distance + 1)
      (Rewind.cfg (markedTape origin xs) (origin + distance)) =
      some (Rewind.cfg (markedTape origin xs) (origin - 1)) ∧
    step (Rewind.program marker) (Rewind.cfg (markedTape origin xs) (origin - 1)) = none := by
  have hnon : ∀ j : ℕ, j < distance + 1 →
      markedTape origin xs (origin + distance - j) ≠ marker := by
    intro j hj
    apply markedTape_ne_marker
    omega
  have hpos : origin + (distance : ℤ) - ((distance + 1 : ℕ) : ℤ) = origin - 1 := by omega
  have hend : markedTape origin xs (origin + distance - (distance + 1 : ℕ)) = marker := by
    rw [hpos]
    exact markedTape_marker origin xs
  have hr := Rewind.rewind_exact marker (markedTape origin xs) (origin + distance)
    (distance + 1) hnon hend
  simpa only [hpos] using hr

end IntegerMultBounds.Machine.PartitionMarked
