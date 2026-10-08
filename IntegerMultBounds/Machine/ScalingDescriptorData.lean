import IntegerMultBounds.Machine.ScalingMergeData
import IntegerMultBounds.Machine.GrowingCounterData
import IntegerMultBounds.Machine.ScalingSplit

/-! Growing binary descriptor families for scaling pieces. The merge selector
routes one block-width batch of increments to exactly one descriptor. Aggregate
carry potential telescopes across the whole family, paying linear total work
without charging the growing binary width separately on every increment. -/

namespace IntegerMultBounds.Machine.ScalingDescriptorData

open GrowingCounterData

/-- The increment iteration has the expected additive composition law. -/
theorem advance_add (m n : ℕ) (bs : List Bool) :
    advance (m+n) bs = advance n (advance m bs) := by
  induction m generalizing bs with
  | zero => simp only [Nat.zero_add,advance]
  | succ m ih => simpa only [Nat.succ_add,advance] using ih (increment bs)

theorem advance_succ_right (n : ℕ) (bs : List Bool) :
    advance (n+1) bs = increment (advance n bs) := by
  rw [advance_add]
  rfl

/-- Binary piece-length descriptors after the first z selected blocks. -/
def descriptors {c : ℕ} (hc : 0 < c) (Q B z : ℕ) (j : Fin c) : List Bool :=
  advance (ScalingMergeData.popCount hc Q z j.val*B) []

@[simp] theorem descriptors_zero {c : ℕ} (hc : 0 < c) (Q B : ℕ) :
    descriptors hc Q B 0 = fun _ => [] := by
  funext j
  simp [descriptors,ScalingMergeData.popCount,advance]

theorem descriptors_value {c : ℕ} (hc : 0 < c) (Q B z : ℕ) (j : Fin c) :
    Counter.value (descriptors hc Q B z j) = ScalingMergeData.popCount hc Q z j.val*B :=
  empty_value _

theorem descriptors_canonical {c : ℕ} (hc : 0 < c) (Q B z : ℕ) (j : Fin c) :
    Canonical (descriptors hc Q B z j) := advance_canonical _ [] (Or.inl rfl)

/-- One batch of B increments changes only the selected piece descriptor. -/
theorem descriptors_step {c : ℕ} (hc : 0 < c) (Q B z : ℕ) :
    Function.update (descriptors hc Q B z) (ScalingControl.select hc Q z)
      (advance B (descriptors hc Q B z (ScalingControl.select hc Q z))) =
      descriptors hc Q B (z+1) := by
  funext j
  by_cases hj : j = ScalingControl.select hc Q z
  · subst j
    simp only [Function.update_self,descriptors,ScalingMergeData.popCount_succ,ite_true,
      Nat.add_mul,one_mul]
    exact (advance_add _ _ []).symm
  · have hv : (ScalingControl.select hc Q z).val ≠ j.val := by
      intro h
      exact hj (Fin.ext h.symm)
    simp only [Function.update_of_ne hj,descriptors,ScalingMergeData.popCount_succ,
      ite_eq_right hv,Nat.add_zero]

/-- Exact cost of all growing-counter calls in one selected block batch. -/
def blockCost {c : ℕ} (hc : 0 < c) (Q B z : ℕ) : ℕ :=
  totalCost B (descriptors hc Q B z (ScalingControl.select hc Q z))

def potential {c : ℕ} (ds : Fin c → List Bool) : ℕ := ∑ j, 2*Counter.weight (ds j)

/-- Every batch pays its true carry/return cost from the family potential. -/
theorem block_potential {c : ℕ} (hc : 0 < c) (Q B z : ℕ) :
    blockCost hc Q B z + potential (descriptors hc Q B (z+1)) =
      4*B + potential (descriptors hc Q B z) := by
  classical
  let j := ScalingControl.select hc Q z
  have hpoint (k : Fin c) :
      (if k = j then blockCost hc Q B z else 0) + 2*Counter.weight (descriptors hc Q B (z+1) k) =
        (if k = j then 4*B else 0) + 2*Counter.weight (descriptors hc Q B z k) := by
    rw [← descriptors_step]
    by_cases hk : k = j
    · subst k
      simp only [j,ite_true,Function.update_self,blockCost]
      exact total_potential B _
    · have hk' : k ≠ ScalingControl.select hc Q z := hk
      simp only [ite_eq_right hk,Function.update_of_ne hk']
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun k _ => hpoint k)
  simpa only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true,potential] using hs

/-- Sum of actual carry and return transitions over all processed blocks. -/
def totalCost {c : ℕ} (hc : 0 < c) (Q B n : ℕ) : ℕ :=
  ∑ z ∈ Finset.range n, blockCost hc Q B z

theorem total_potential {c : ℕ} (hc : 0 < c) (Q B n : ℕ) :
    totalCost hc Q B n + potential (descriptors hc Q B n) = 4*(n*B) := by
  induction n with
  | zero => simp [totalCost,descriptors_zero,potential,Counter.weight]
  | succ n ih =>
    have hs := block_potential hc Q B n
    simp only [totalCost,Finset.sum_range_succ] at *
    nlinarith

theorem amortized_cost {c : ℕ} (hc : 0 < c) (Q B n : ℕ) :
    totalCost hc Q B n ≤ 4*(n*B) := by
  have h := total_potential hc Q B n
  omega

/-- At completion, every canonical descriptor counts its exact contiguous
piece length. Coprimality is used only for the selector's complete counts. -/
theorem complete_value {Q c B : ℕ} (hQ : 0 < Q) (hc : 0 < c) (hcop : c.Coprime Q)
    (j : Fin c) :
    Counter.value (descriptors hc Q B Q j) =
      (ScalingControl.boundary Q c (j.val+1)-ScalingControl.boundary Q c j.val)*B := by
  rw [descriptors_value,ScalingMergeData.complete_count hQ hc hcop]

theorem complete_piece_length {Q c B : ℕ} (hQ : 0 < Q) (hc : 0 < c) (hcop : c.Coprime Q)
    (input : List (Fin 4)) (hlen : input.length = Q*B) (j : Fin c) :
    Counter.value (descriptors hc Q B Q j) = (ScalingSplit.piece Q c B input j).length := by
  rw [complete_value hQ hc hcop,ScalingSplit.piece_length hc input hlen]
  simp only [ScalingSplit.offset,Nat.sub_mul]

end IntegerMultBounds.Machine.ScalingDescriptorData
