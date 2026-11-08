module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! The manuscript partitions source rows by target cores:
J_k = [floor(k*L*s/t), floor((k+1)*L*s/t)). These source cores need not
have equal lengths. No nearest-row ownership convention is substituted. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership
open scoped BigOperators

def cut (s t L k : ℕ) := k*L*s/t
def rows (s t L k : ℕ) := cut s t L (k+1)-cut s t L k

theorem cut_mono (s t L : ℕ) : Monotone (cut s t L) := by
  intro i j hij
  exact Nat.div_le_div_right (Nat.mul_le_mul_right s (Nat.mul_le_mul_right L hij))

@[simp] theorem cut_zero (s t L : ℕ) : cut s t L 0 = 0 := by simp [cut]

theorem cut_last (s t L Q : ℕ) (ht : 0 < t) (hQ : Q*L = t) : cut s t L Q = s := by
  dsimp only [cut]
  rw [hQ,Nat.mul_div_cancel_left s ht]

theorem rows_le (s t L k : ℕ) (ht : 0 < t) (hst : s ≤ t) : rows s t L k ≤ L := by
  have hmul := Nat.mul_le_mul_left L hst
  have hh : (k+1)*L*s ≤ k*L*s+L*t := by nlinarith only [hmul]
  have hd := Nat.div_le_div_right (c := t) hh
  rw [Nat.add_mul_div_right _ _ ht] at hd
  dsimp only [rows,cut]
  omega

theorem rows_pos (s t L k : ℕ) (ht : 0 < t) (hnear : t ≤ 2*s) (hL : 2 ≤ L) :
    0 < rows s t L k := by
  have hstep : t ≤ L*s := hnear.trans (Nat.mul_le_mul_right s hL)
  have hbase := Nat.div_mul_le_self (k*L*s) t
  have hnext : (k*L*s/t)+1 ≤ (k+1)*L*s/t := by
    apply (Nat.le_div_iff_mul_le ht).mpr
    nlinarith only [hbase,hstep]
  dsimp only [rows,cut]
  omega

theorem rows_sum (s t L Q : ℕ) : (∑ k ∈ Finset.range Q, rows s t L k) = cut s t L Q := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [Finset.sum_range_succ,ih]
    have hm := cut_mono s t L (show Q ≤ Q+1 by omega)
    dsimp only [rows]
    omega

theorem owns_exists (s t L Q j : ℕ) (hj : j < cut s t L Q) :
    ∃ k < Q, cut s t L k ≤ j ∧ j < cut s t L (k+1) := by
  induction Q with
  | zero => simp at hj
  | succ Q ih =>
    by_cases h : j < cut s t L Q
    · obtain ⟨k,hk,ha,hb⟩ := ih h
      exact ⟨k,by omega,ha,hb⟩
    · exact ⟨Q,by omega,by omega,hj⟩

theorem owns_unique (s t L j k l : ℕ)
    (hk : cut s t L k ≤ j ∧ j < cut s t L (k+1))
    (hl : cut s t L l ≤ j ∧ j < cut s t L (l+1)) : k = l := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hm := cut_mono s t L (show k+1 ≤ l by omega)
    omega
  · have hm := cut_mono s t L (show l+1 ≤ k by omega)
    omega

/-- Exact coverage and unique ownership, including potentially empty cores. -/
theorem partition (s t L Q : ℕ) (ht : 0 < t) (hQ : Q*L = t) (j : ℕ) (hj : j < s) :
    ∃! k, k < Q ∧ cut s t L k ≤ j ∧ j < cut s t L (k+1) := by
  have hlast := cut_last s t L Q ht hQ
  obtain ⟨k,hk,ha,hb⟩ := owns_exists s t L Q j (by omega)
  refine ⟨k,⟨hk,ha,hb⟩,?_⟩
  intro l hl
  exact owns_unique s t L j l k hl.2 ⟨ha,hb⟩

end IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership
