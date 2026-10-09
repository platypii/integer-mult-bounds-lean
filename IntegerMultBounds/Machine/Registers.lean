import IntegerMultBounds.Machine.GrowingCounterData
import IntegerMultBounds.Machine.ExactFrame
import IntegerMultBounds.Machine.WordMoves
import Mathlib.Data.List.GetD

/-! Natural-number registers on tapes. A register holding `n` is the canonical
binary word of `n` (least significant bit first, no high zeros) at origin
zero with the head there. Canonical words are unique for their value, and a
trim machine removes high zeros from any word. -/

namespace IntegerMultBounds.Machine.Registers

open GrowingCounterData (Canonical advance)

variable {a : ℕ}

/-- The canonical binary word of `n`. -/
def canon (n : ℕ) : List Bool := advance n []

theorem canon_value (n : ℕ) : Counter.value (canon n) = n := GrowingCounterData.empty_value n

theorem canon_canonical (n : ℕ) : Canonical (canon n) := GrowingCounterData.advance_canonical n [] (Or.inl rfl)

theorem value_snoc_true (ys : List Bool) : 0 < Counter.value (ys ++ [true]) := by
  induction ys with
  | nil => simp [Counter.value]
  | cons b ys ih => cases b <;> simp [Counter.value] <;> omega

theorem value_eq_zero_of_canonical (xs : List Bool) (h : Canonical xs) (hv : Counter.value xs = 0) : xs = [] := by
  rcases h with h | h
  · exact h
  · exfalso
    obtain ⟨ys, rfl⟩ : ∃ ys, xs = ys ++ [true] := by
      rcases List.eq_nil_or_concat xs with h0 | ⟨L, b, rfl⟩
      · subst h0; simp at h
      · simp at h; exact ⟨L, by rw [h]; simp⟩
    have := value_snoc_true ys
    omega

theorem canonical_tail (b : Bool) (xs : List Bool) (h : Canonical (b :: xs)) : Canonical xs := by
  rcases h with h | h
  · simp at h
  · rcases xs with _ | ⟨c, xs⟩
    · exact Or.inl rfl
    · right; simpa [List.getLast?_cons_cons] using h

/-- Canonical words are determined by their value. -/
theorem canonical_unique (xs ys : List Bool) (hx : Canonical xs) (hy : Canonical ys)
    (h : Counter.value xs = Counter.value ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => exact (value_eq_zero_of_canonical ys hy (by simpa [Counter.value] using h.symm)).symm
  | cons b xs ih =>
    cases ys with
    | nil => exact value_eq_zero_of_canonical _ hx (by simpa [Counter.value] using h)
    | cons c ys =>
      simp only [Counter.value] at h
      have hbc : b = c := by
        rcases b with _ | _ <;> rcases c with _ | _
        · rfl
        · simp at h; omega
        · simp at h; omega
        · rfl
      subst hbc
      have : Counter.value xs = Counter.value ys := by cases b <;> simp at h <;> omega
      rw [ih ys (canonical_tail b xs hx) (canonical_tail b ys hy) this]

theorem canon_of_canonical (xs : List Bool) (h : Canonical xs) : xs = canon (Counter.value xs) :=
  canonical_unique _ _ h (canon_canonical _) (canon_value _).symm

/-- The register tape of `n` (one tape, origin zero). -/
def reg (n : ℕ) : ℤ → Fin (a + 4) := putWord (fun _ => blank) 0 ((canon n).map bitSymbol)

/-- One-tape banks. -/
def one (f : ℤ → Fin (a + 4)) (p : ℤ) : Tapes 1 a := ⟨fun _ => p, fun _ => f⟩

namespace EraseZeros

/-- Erase high zero bits leftwards; stop on anything else. -/
def program : Program 1 1 a where
  tapes_pos := by decide
  start := 0
  transition := fun _ sy => if sy 0 = bitSymbol false then some (0, fun _ => (blank, .left)) else none

theorem bits_ne_false (b : Bool) (hb : b = true) : (bitSymbol b : Fin (a + 4)) ≠ bitSymbol false := by
  subst hb; simp [bitSymbol]

theorem pw_elem (f : ℤ → Fin (a + 4)) (p : ℤ) (xs : List (Fin (a + 4))) (k : ℕ)
    (hk : k < xs.length) : putWord f p xs (p + k) = xs[k] := by
  induction xs generalizing f p k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero => simp [putWord_head]
    | succ k =>
      rw [putWord_cons, show p + ((k + 1 : ℕ) : ℤ) = p + 1 + k by omega,
        ih _ (p + 1) k (by simpa using hk)]
      rfl

theorem pw_get (L : List (Fin (a + 4))) (k : ℕ) : putWord (fun _ => blank) 0 L (k : ℤ) = L.getD k blank := by
  rcases Nat.lt_or_ge k L.length with h | h
  · have := pw_elem (fun _ => (blank : Fin (a + 4))) 0 L k h
    rw [zero_add] at this
    rw [this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  · rw [putWord_outside _ _ _ _ (Or.inr (by omega)), List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
    rfl

/-- Writing a blank over the last symbol of a word on a blank background drops it. -/
theorem pw_drop_last (L : List (Fin (a + 4))) (x : Fin (a + 4)) :
    (fun j => if j = ((L.length : ℕ) : ℤ) then blank else putWord (fun _ => blank) 0 (L ++ [x]) j) =
      putWord (fun _ => blank) 0 L := by
  funext j
  split_ifs with hj
  · rw [hj, putWord_outside _ _ _ _ (Or.inr (by simp))]
  · rcases lt_or_ge j 0 with h0 | h0
    · rw [putWord_outside _ _ _ _ (Or.inl h0), putWord_outside _ _ _ _ (Or.inl h0)]
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = k := ⟨j.toNat, by omega⟩
      have hk : k ≠ L.length := by intro h; exact hj (by rw [h])
      rw [pw_get, pw_get]
      rcases Nat.lt_or_ge k L.length with h | h
      · rw [List.getD_append _ _ _ _ h]
      · rw [List.getD_append_right _ _ _ _ h, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none h, List.getElem?_eq_none (by simp; omega)]

theorem erase_run (ys : List Bool) (n : ℕ) :
    run (program (a := a)) n ⟨0, fun _ => (((ys.length + n : ℕ) : ℤ) - 1),
        fun _ => putWord (fun _ => blank) 0 ((ys ++ List.replicate n false).map bitSymbol)⟩ =
      some ⟨0, fun _ => ((ys.length : ℕ) : ℤ) - 1, fun _ => putWord (fun _ => blank) 0 (ys.map bitSymbol)⟩ := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    rw [run]
    set L := (ys ++ List.replicate n false).map (bitSymbol (a := a))
    have hL : (ys ++ List.replicate (n + 1) false).map (bitSymbol (a := a)) = L ++ [bitSymbol false] := by
      simp only [L, List.replicate_succ', ← List.append_assoc, List.map_append, List.map_singleton]
    have hLl : L.length = ys.length + n := by simp [L]
    have hpos : (((ys.length + (n + 1) : ℕ) : ℤ) - 1) = ((L.length : ℕ) : ℤ) := by rw [hLl]; push_cast; ring
    have hread : putWord (fun _ => (blank : Fin (a + 4))) 0 (L ++ [bitSymbol false]) ((L.length : ℕ) : ℤ) =
        bitSymbol false := by
      rw [pw_get, List.getD_append_right _ _ _ _ le_rfl]; simp
    have hstep : step (program (a := a)) ⟨0, fun _ => (((ys.length + (n + 1) : ℕ) : ℤ) - 1),
        fun _ => putWord (fun _ => blank) 0 ((ys ++ List.replicate (n + 1) false).map bitSymbol)⟩ =
        some ⟨0, fun _ => (((ys.length + n : ℕ) : ℤ) - 1), fun _ => putWord (fun _ => blank) 0 L⟩ := by
      unfold step
      rw [hL, hpos]
      simp only [program, hread, ↓reduceIte, Move.offset, Option.some.injEq, Config.mk.injEq, true_and]
      refine ⟨by funext _; rw [hLl]; push_cast; ring, ?_⟩
      funext _
      exact pw_drop_last L _
    rw [hstep]
    simp only [Option.bind_some]
    exact ih

/-- Erasing the high zeros of `ys ++ 0^n` from its last cell. -/
theorem erase_hoare (ys : List Bool) (n : ℕ) (hy : Canonical ys) :
    HoareTime (program (a := a))
      (fun v => v = one (putWord (fun _ => blank) 0 ((ys ++ List.replicate n false).map bitSymbol))
        (((ys.length + n : ℕ) : ℤ) - 1))
      (fun v => v = one (putWord (fun _ => blank) 0 (ys.map bitSymbol)) (((ys.length : ℕ) : ℤ) - 1)) n := by
  rintro v rfl
  refine ⟨n, _, le_rfl, erase_run ys n, ?_, rfl⟩
  have hnot : putWord (fun _ => (blank : Fin (a + 4))) 0 (ys.map bitSymbol) (((ys.length : ℕ) : ℤ) - 1) ≠
      bitSymbol false := by
    rcases hy with h | h
    · subst h; simp [putWord, bitSymbol, blank]
    · obtain ⟨zs, rfl⟩ : ∃ zs, ys = zs ++ [true] := by
        rcases List.eq_nil_or_concat ys with h0 | ⟨L, b, rfl⟩
        · subst h0; simp at h
        · simp at h; exact ⟨L, by rw [h]; simp⟩
      rw [show (((zs ++ [true]).length : ℕ) : ℤ) - 1 = ((zs.length : ℕ) : ℤ) by simp, pw_get]
      simp [List.getD_append_right, bitSymbol]
  simp [step, program, hnot]

end EraseZeros

namespace Trim

/-- Remove high zeros from a register word. -/
def program :=
  seq (seq (seq (seq (ScanEnd.program (a := a)) (StepLeft.program (a := a))) (EraseZeros.program (a := a)))
    (StepRight.program (a := a))) (ReturnOrigin.program (a := a))

theorem bits_nb (xs : List Bool) : ∀ x ∈ xs.map (bitSymbol (a := a)), x ≠ blank := ReturnOrigin.bits_nonblank _

theorem trim_hoare (ys : List Bool) (n : ℕ) (hy : Canonical ys) :
    HoareTime (program (a := a))
      (fun v => v = one (putWord (fun _ => blank) 0 ((ys ++ List.replicate n false).map bitSymbol)) 0)
      (fun v => v = one (putWord (fun _ => blank) 0 (ys.map bitSymbol)) 0) (2 * ys.length + 2 * n + 10) := by
  set F := putWord (fun _ => (blank : Fin (a + 4))) 0 ((ys ++ List.replicate n false).map bitSymbol)
  set G := putWord (fun _ => (blank : Fin (a + 4))) 0 (ys.map bitSymbol)
  have h1 : HoareTime (ScanEnd.program (a := a)) (fun v => v = one F 0)
      (fun v => v = one F (((ys.length + n : ℕ) : ℤ))) (ys.length + n) := by
    have := ScanEnd.scan_hoare (fun _ => (blank : Fin (a + 4))) 0 ((ys ++ List.replicate n false).map bitSymbol)
      (bits_nb _) rfl
    simp only [List.length_map, List.length_append, List.length_replicate, zero_add] at this
    exact this
  have h2 : HoareTime (StepLeft.program (a := a)) (fun v => v = one F (((ys.length + n : ℕ) : ℤ)))
      (fun v => v = one F (((ys.length + n : ℕ) : ℤ) - 1)) 1 := StepLeft.step_hoare F _
  have h3 := EraseZeros.erase_hoare (a := a) ys n hy
  have h4 : HoareTime (StepRight.program (a := a)) (fun v => v = one G (((ys.length : ℕ) : ℤ) - 1))
      (fun v => v = one G ((ys.length : ℕ) : ℤ)) 1 := by
    have := StepRight.step_hoare G (((ys.length : ℕ) : ℤ) - 1)
    rw [sub_add_cancel] at this
    exact this
  have h5 : HoareTime (ReturnOrigin.program (a := a)) (fun v => v = one G ((ys.length : ℕ) : ℤ))
      (fun v => v = one G 0) (ys.length + 2) := by
    have := ReturnOrigin.return_hoare_at (fun _ => (blank : Fin (a + 4))) 0 (ys.map bitSymbol) (bits_nb _) rfl
    simp only [List.length_map, zero_add] at this
    exact this
  exact (((((h1.seq h2).seq h3).seq h4).seq h5)).consequence (fun v hv => hv) (fun v hv => hv) (by omega)

end Trim

theorem canonical_split (xs : List Bool) :
    ∃ ys : List Bool, ∃ n : ℕ, xs = ys ++ List.replicate n false ∧ Canonical ys := by
  induction xs using List.reverseRecOn with
  | nil => exact ⟨[], 0, rfl, Or.inl rfl⟩
  | append_singleton xs b ih =>
    cases b
    · obtain ⟨ys, n, he, hc⟩ := ih
      refine ⟨ys, n + 1, ?_, hc⟩
      rw [he, List.replicate_succ', List.append_assoc]
    · exact ⟨xs ++ [true], 0, by simp, Or.inr (by simp)⟩

theorem value_padding (ys : List Bool) (n : ℕ) : Counter.value (ys ++ List.replicate n false) = Counter.value ys := by
  induction ys with
  | nil =>
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, Counter.value] at ih ⊢; exact ih
  | cons b ys ih => simp [Counter.value, ih]

/-- Normalizing any word gives the register of its value. -/
theorem norm_hoare (xs : List Bool) :
    HoareTime (Trim.program (a := a)) (fun v => v = one (putWord (fun _ => blank) 0 (xs.map bitSymbol)) 0)
      (fun v => v = one (reg (Counter.value xs)) 0) (2 * xs.length + 10) := by
  obtain ⟨ys, n, rfl, hy⟩ := canonical_split xs
  have h := Trim.trim_hoare (a := a) ys n hy
  refine h.consequence (fun v hv => hv) (fun v hv => ?_) (by simp; omega)
  rw [hv, value_padding]
  unfold reg
  rw [← canon_of_canonical ys hy]

end IntegerMultBounds.Machine.Registers
