import IntegerMultBounds.Resampling.RowSelect
import IntegerMultBounds.Machine.NeumannLoop
import IntegerMultBounds.Machine.PairJoin

/-! Word lists for the numerical `B̃₀` on tapes: the selected words of the
row-selecting map (the joined pairs at the selected indices split again),
and the one-step maps with window radius zero used for the halving and for
`D̃'`. -/

namespace IntegerMultBounds.Resampling.B0Words

open IntegerMultBounds.Machine
open IntegerMultBounds.Machine.OrderedSelect (inTape flat)
open IntegerMultBounds.Machine.GaussianLine (wordRecs outWords)
open IntegerMultBounds.Machine.PairJoin (pairs)
open IntegerMultBounds.Resampling.NeumannWords (ext nextWords)
open IntegerMultBounds.NLogN (rowIndexNat)

variable {a : ℕ}

/-- The words of the selected coordinates: real and imaginary word of the
input coordinate `rowIndexNat s t j`, for `j < s`. -/
noncomputable def vsel (win : List (List Bool)) (s t : ℕ) : List (List Bool) :=
  (List.range s).flatMap fun j : ℕ =>
    [win.getD (2 * rowIndexNat s t (j : ZMod s)) [], win.getD (2 * rowIndexNat s t (j : ZMod s) + 1) []]

/-- One step with window radius zero and zero start words. -/
def oneStep (wt zeros : List (List Bool)) (s p w : ℕ) (y : List (List Bool)) : List (List Bool) :=
  nextWords zeros (outWords wt (ext s 0 y) s s 0 p w w s) w

theorem oneStep_eq (wt zeros : List (List Bool)) (s p w : ℕ) (y : List (List Bool)) :
    nextWords zeros (outWords wt (ext s 0 y) s s 0 p w w s) w = oneStep wt zeros s p w y := rfl

theorem pairs_flatMap (L : List ℕ) (f g : ℕ → List Bool) :
    pairs (a := a) (L.flatMap fun j => [f j, g j]) =
      L.map fun j => (f j).map bitSymbol ++ separator :: (g j).map bitSymbol := by
  induction L with
  | nil => rfl
  | cons j L ih => simp [List.flatMap_cons, pairs, ih]

theorem pairs_getD (win : List (List Bool)) (q : ℕ) (hq : 2 * q + 1 < win.length) :
    (pairs (a := a) win).getD q [] =
      (win.getD (2 * q) []).map bitSymbol ++ separator :: (win.getD (2 * q + 1) []).map bitSymbol := by
  induction q generalizing win with
  | zero =>
    match win, hq with
    | x :: y :: rest, _ => simp [pairs]
  | succ q ih =>
    match win, hq with
    | x :: y :: rest, hq =>
      simp only [pairs, List.getD_cons_succ]
      rw [ih rest (by simp at hq; omega)]
      simp [show 2 * (q + 1) = 2 * q + 1 + 1 by ring]

theorem pairs_length (n : ℕ) : ∀ win : List (List Bool), win.length = 2 * n → (pairs (a := a) win).length = n := by
  induction n with
  | zero => intro win h; obtain rfl : win = [] := List.length_eq_zero_iff.mp (by omega); rfl
  | succ n ih =>
    intro win h
    match win, h with
    | x :: y :: rest, h => simp [pairs, ih rest (by simp at h; omega)]

theorem pairs_mem (n : ℕ) : ∀ win : List (List Bool), win.length = 2 * n → (∀ x ∈ win, x ≠ []) →
    ∀ r ∈ pairs (a := a) win, r ≠ [] ∧ ∀ c ∈ r, c ≠ blank := by
  induction n with
  | zero => intro win h; obtain rfl : win = [] := List.length_eq_zero_iff.mp (by omega); simp [pairs]
  | succ n ih =>
    intro win h hne
    match win, h with
    | x :: y :: rest, h =>
      intro r hr
      simp only [pairs, List.mem_cons] at hr
      rcases hr with rfl | hr
      · refine ⟨by simp, fun c hc => ?_⟩
        simp only [List.mem_append, List.mem_cons, List.mem_map] at hc
        rcases hc with ⟨b, _, rfl⟩ | rfl | ⟨b, _, rfl⟩
        · cases b <;> simp [bitSymbol, blank]
        · exact PairJoin.sep_ne_blank
        · cases b <;> simp [bitSymbol, blank]
      · exact ih rest (by simp at h; omega) (fun z hz => hne z (by simp [hz])) r hr

variable (s t : ℕ) [NeZero s] (hst : s < t)

include hst in
theorem sel_eq (win : List (List Bool)) (hwin : win.length = 2 * t) :
    (List.range s).map (fun j : ℕ => (pairs (a := a) win).getD (rowIndexNat s t (j : ZMod s)) []) =
      pairs (a := a) (vsel win s t) := by
  unfold vsel
  rw [pairs_flatMap (a := a)]
  refine List.map_congr_left fun j _ => ?_
  have := NLogN.rowIndexNat_lt (s := s) (t := t) hst (j : ZMod s)
  exact pairs_getD win _ (by omega)

omit [NeZero s] in
theorem vsel_length (win : List (List Bool)) : (vsel win s t).length = 2 * s := by
  simp [vsel, List.length_flatMap]; ring

include hst in
theorem vsel_width (win : List (List Bool)) (w : ℕ) (hwin : win.length = 2 * t)
    (hw : ∀ x ∈ win, x.length = w) : ∀ x ∈ vsel win s t, x.length = w := by
  intro x hx
  simp only [vsel, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hx
  obtain ⟨j, hj, rfl | rfl⟩ := hx
  all_goals
    have := NLogN.rowIndexNat_lt (s := s) (t := t) hst (j : ZMod s)
    exact hw _ (NeumannWords.getD_mem' _ _ (by omega))

end IntegerMultBounds.Resampling.B0Words
