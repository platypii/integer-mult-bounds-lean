module

public import IntegerMultBounds.MathlibTM2.Fast.RingProdStock
import Mathlib.Tactic.Ring

/-! Shared ring-product stock separates one product reserve from header and digit volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Schoenhage IntegerMultBounds.Schoenhage.Tp
  IntegerMultBounds.Schoenhage.Schedule IntegerMultBounds.Spec.SignedRingProduct

@[irreducible] def ringHeaderScale (p l w : ℕ) : ℕ :=
  p+l+w+wOf p l w+p.size+(2^l).size+w.size+1

theorem ringCoreWorkspace_zero_le (p l w H : ℕ) :
    ringCoreWorkspace p l w H 0 ≤
      12*cost cA cB cC0 (wOf p l w*2^l)+
        1000000*(H+(ringHeaderScale p l w)^2+2^l*ringHeaderScale p l w+1) := by
  unfold ringCoreWorkspace ringRecordCost ringCost headerCost constCost
    ringSharedBankStock ringConstantStock ringHeaderScale
  dsimp only
  ring_nf
  omega

theorem rpWorkspace_zero_le (p l w : ℕ) :
    rpWorkspace p l w 0 ≤
      12*cost cA cB cC0 (wOf p l w*2^l)+
        1000000*((header p (2^l) w).length+(ringHeaderScale p l w)^2+
          2^l*ringHeaderScale p l w+1)+8*(header p (2^l) w).length+141 := by
  have h := ringCoreWorkspace_zero_le p l w (header p (2^l) w).length
  unfold rpWorkspace rpHostWorkspace
  dsimp only
  simpa only [Nat.mul_zero,Nat.zero_mul,Nat.add_zero,Nat.add_assoc,Nat.reduceAdd] using Nat.add_le_add_right h
    (8*(header p (2^l) w).length+141)

theorem ringDigitWidth_le (p l w : ℕ) : wOf p l w ≤ 8*(p+l+w+1) := by
  have ht := (topN_facts (show 1 ≤ mW p l w+1 by omega)).2.1
  calc
    _ ≤ 2^Nat.size (2*(mW p l w+1)) := by
      unfold wOf
      exact Nat.pow_le_pow_right (by decide) (Nat.size_le_size (by omega))
    _ ≤ 4*(mW p l w+1) := by simpa only [topN,bitlen] using ht
    _ ≤ _ := by unfold mW; omega

theorem ringHeaderScale_le (p l w : ℕ) : ringHeaderScale p l w ≤ 12*(p+l+w+1) := by
  have hW := ringDigitWidth_le p l w
  have hp := Nat.size_le.mpr (Nat.lt_two_pow_self (n := p))
  have hw := Nat.size_le.mpr (Nat.lt_two_pow_self (n := w))
  unfold ringHeaderScale
  rw [Nat.size_pow]
  omega

theorem ringScheduleCost_le (p l w : ℕ) :
    let N := 8*(p+l+w+1)*2^l
    cost cA cB cC0 (wOf p l w*2^l) ≤
      costC cA cB cC0*(N+1)*(N.size+1)*((N.size^3).size+1) := by
  dsimp only
  have hN := Nat.mul_le_mul_right (2^l) (ringDigitWidth_le p l w)
  have hsize := Nat.size_le_size hN
  have hcube : (wOf p l w*2^l).size^3 ≤ (8*(p+l+w+1)*2^l).size^3 := by gcongr
  have hlog := Nat.size_le_size hcube
  apply (cost_le cA cB cC0 (wOf p l w*2^l)).trans
  simp only [bitlen]
  gcongr

theorem rpWorkspace_zero_le_dimensions (p l w : ℕ) :
    rpWorkspace p l w 0 ≤
      12*cost cA cB cC0 (wOf p l w*2^l)+
      1000000*(2*(p+2^l+w)+(12*(p+l+w+1))^2+2^l*(12*(p+l+w+1))+1)+
      16*(p+2^l+w)+141 := by
  apply (rpWorkspace_zero_le p l w).trans
  have hH := ring_header_length_le p (2^l) w
  have hD := ringHeaderScale_le p l w
  have hH' : 8*(header p (2^l) w).length ≤ 16*(p+2^l+w) := by
    simpa only [← Nat.mul_assoc] using Nat.mul_le_mul_left 8 hH
  gcongr

@[irreducible] def ringWorkspaceBudget (p l w : ℕ) : ℕ :=
  let N := 8*(p+l+w+1)*2^l
  12*costC cA cB cC0*(N+1)*(N.size+1)*((N.size^3).size+1)+
    1000000*(2*(p+2^l+w)+(12*(p+l+w+1))^2+2^l*(12*(p+l+w+1))+1)+
    16*(p+2^l+w)+141

theorem rpWorkspace_zero_le_budget (p l w : ℕ) :
    rpWorkspace p l w 0 ≤ ringWorkspaceBudget p l w := by
  apply (rpWorkspace_zero_le_dimensions p l w).trans
  have h := Nat.mul_le_mul_left 12 (ringScheduleCost_le p l w)
  unfold ringWorkspaceBudget
  dsimp only at h ⊢
  simpa only [Nat.mul_assoc] using Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right h _) _) _

end IntegerMultBounds.MathlibTM2.Fast
