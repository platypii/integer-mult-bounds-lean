import IntegerMultBounds.Machine.RepeatedWeightedPhaseAccumulator

/-! Algebraic interchange connects the single weight-block-major control scan
to the product of the per-coordinate-axis phases. -/
namespace IntegerMultBounds.Machine.RepeatedWeightedPhaseTensor
noncomputable section
open WeightedPhaseAccumulator (weightedSum)
open RepeatedWeightedPhaseAccumulator (total)

private theorem zip_ofFn {α β γ : Type*} {n : ℕ} (f : α → β → γ) (x : Fin n → α) (y : Fin n → β) :
    List.zipWith f (List.ofFn x) (List.ofFn y)=List.ofFn (fun i => f (x i) (y i)) := by
  apply List.ext_getElem (by simp)
  intro j hj hk
  simp only [List.getElem_zipWith,List.getElem_ofFn]

theorem weightedSum_eq_sum (ws : List (ZMod 4)) (bs : List Bool) (hl : bs.length=ws.length) :
    weightedSum ws bs=∑ i : Fin ws.length,if bs.getD i.val false then ws.getD i.val 0 else 0 := by
  have hw : List.ofFn (fun i : Fin ws.length => ws.getD i.val 0)=ws := by
    apply List.ext_getElem (by simp)
    intro j hj hk
    simp only [List.getElem_ofFn]
    rw [List.getD_eq_getElem _ _ hk]
  have hb : List.ofFn (fun i : Fin ws.length => bs.getD i.val false)=bs := by
    apply List.ext_getElem (by simp [hl])
    intro j hj hk
    simp only [List.getElem_ofFn]
    rw [List.getD_eq_getElem _ _ hk]
  unfold weightedSum
  conv_lhs => rw [←hw,←hb,zip_ofFn,List.sum_ofFn]

theorem total_eq_fin_sum (ws : List (ZMod 4)) (bits : ℕ → Bool) (n : ℕ) :
    total ws bits n=∑ i : Fin ws.length,∑ j : Fin n,
      if bits (i.val*n+j.val) then ws.getD i.val 0 else 0 := by
  rw [RepeatedWeightedPhaseAccumulator.total_eq_sum,←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [←Fin.sum_univ_eq_sum_range]

/-- Interchanging finite sums pays no extra tape traversal. -/
theorem matrix_total (ws : List (ZMod 4)) (bits : ℕ → Bool) (n : ℕ)
    (columns : Fin n → List Bool) (hl : ∀ j,(columns j).length=ws.length)
    (hb : ∀ (i : Fin ws.length) (j : Fin n),
      bits (i.val*n+j.val)=(columns j).getD i.val false) :
    total ws bits n=∑ j : Fin n,weightedSum ws (columns j) := by
  rw [total_eq_fin_sum,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [weightedSum_eq_sum ws (columns j) (hl j)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hb i j]

end
end IntegerMultBounds.Machine.RepeatedWeightedPhaseTensor
