module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutedData

/-! # Rowwise and flattened execution of the normalized input stream -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast

theorem zipWith_flatMap_rows {α β γ : Type*} (f : α → β → γ) (rows : List ℕ)
    (X : ℕ → List α) (Y : ℕ → List β) (hlen : ∀ n ∈ rows, (X n).length = (Y n).length) :
    List.zipWith f (rows.flatMap X) (rows.flatMap Y) =
      rows.flatMap (fun n => List.zipWith f (X n) (Y n)) := by
  induction rows with
  | nil => simp
  | cons n rows ih =>
    simp only [List.flatMap_cons]
    rw [List.zipWith_append (hlen n (by simp)), ih (fun n hn => hlen n (by simp [hn]))]

theorem weightedInputNumerators_flatMap (q cExp e : ℕ) (rows : List ℕ)
    (X : ℕ → List GaussianInt) (D : ℕ → List ℚ) (hlen : ∀ n ∈ rows, (X n).length = (D n).length) :
    weightedInputNumerators q cExp e (rows.flatMap X) (rows.flatMap D) =
      rows.flatMap (fun n => weightedInputNumerators q cExp e (X n) (D n)) := by
  have hd : reciprocalWeightWords q (rows.flatMap D) =
      rows.flatMap (fun n => reciprocalWeightWords q (D n)) := by
    simp only [reciprocalWeightWords, List.map_flatMap, Function.comp_apply]
  unfold weightedInputNumerators
  rw [hd]
  apply zipWith_flatMap_rows
  intro n hn
  simpa only [reciprocalWeightWords, List.length_map] using hlen n hn

/-- The closed input-weight pass emits exactly the raw bank consumed by S1. -/
theorem executedInputRows_flatMap (s t p u q M L cExp : ℕ) (lo : ℕ → ZMod s)
    (C : ℕ → ZMod s → GaussianInt) :
    weightedInputNumerators q cExp (8 * p + 1)
      ((List.range M).flatMap (cellSourceRows L lo C))
      ((List.range M).flatMap (cellWeightRows s t p u L lo)) =
      (List.range M).flatMap (executedInputRows s t p u q L cExp lo C) := by
  exact weightedInputNumerators_flatMap q cExp (8 * p + 1) (List.range M) _ _ (by intros; simp)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
