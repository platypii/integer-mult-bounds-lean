import IntegerMultBounds.Machine.ArbitraryWidthHighBudget

/-! Runtime high-row metadata construction is paid even before the branch
choosing fast interchange or the bounded elementary fallback. Its rounded
row count is uniformly bounded by a fixed multiple of the original volume. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighMetadataBudget
noncomputable section
open ArbitraryWidthHighPrepare
open RecursiveInterchangeLayout (Descriptor volume)

def constant (q cutoff : ℕ) := 2+2*(q*q)*divisor cutoff

theorem divisor_monotone : Monotone divisor := by
  intro e f hef
  exact Nat.pow_le_pow_right (le_trans (by decide : 1 ≤ base) worlds_ge_base)
    (Nat.clog_mono_right base hef)

/-- Any cutoff certified for the large-width branch also bounds all
metadata generated during the elementary fallback. -/
theorem rounded_bound (q cutoff e : ℕ) (hq : 2 ≤ q)
    (hcut : ∀ n, cutoff ≤ n → highDepth q n ≤ n) :
    rounded q e ≤ constant q cutoff*q^(2*e) := by
  have hpow : 1 ≤ q^(2*e) := Nat.one_le_pow _ _ (by omega : 1 ≤ q)
  by_cases hr : highDepth q e ≤ e
  · have hz := RoundedRowDescriptor.rounded_lt_twice (rows q e) (divisor e)
      (rows_positive q e hq) (divisor_le_rows q e hq)
    change rounded q e < 2*rows q e at hz
    have hp : rows q e ≤ q^(2*e) := by
      rw [rows_eq_high_rows,ArbitraryWidthHighRows.rowCount]
      exact Nat.pow_le_pow_right (by omega : 1 ≤ q) (Nat.mul_le_mul_left 2 hr)
    have hc : 2 ≤ constant q cutoff := by unfold constant; omega
    exact (show rounded q e ≤ 2*q^(2*e) by omega).trans (Nat.mul_le_mul_right _ hc)
  · have he : e ≤ cutoff := by
      by_contra hn
      have := hcut e (by omega)
      exact hr this
    have hd := divisor_monotone he
    have hz := ArbitraryWidthHighPrepare.rounded_bound q e hq
    have hb : rounded q e ≤ constant q cutoff := by
      unfold constant
      have hm := Nat.mul_le_mul_left (2*(q*q)) hd
      omega
    exact hb.trans (Nat.le_mul_of_pos_right _ (by omega : 0 < q^(2*e)))

theorem volume_lower (q : ℕ) (_hq : 2 ≤ q) (v : Descriptor) (hp : v.Positive) :
    q^(2*v.width) ≤ volume q v := by
  let outer := v.beforeRows*v.rows*v.beforeH*v.between*v.afterD
  have ho : 0 < outer := by
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hp.1 hp.2.1) hp.2.2.1) hp.2.2.2.1) hp.2.2.2.2
  calc
    q^(2*v.width) = 1*q^(2*v.width) := by simp
    _ ≤ outer*q^(2*v.width) := Nat.mul_le_mul_right _ (by omega)
    _ = volume q v := by
      unfold volume outer
      have he : q^(2*v.width) = q^v.width*q^v.width := by
        rw [← pow_add]; congr 1; omega
      rw [he]
      ring

/-- A single fixed coefficient bounds high-row metadata on every positive
array, regardless of whether its width takes the fast or fallback branch. -/
theorem uniform_volume_bound (q : ℕ) (hq : 2 ≤ q) :
    ∃ C : ℕ, 0 < C ∧ ∀ v : Descriptor, v.Positive → rounded q v.width ≤ C*volume q v := by
  obtain ⟨cutoff,hcut⟩ := ArbitraryWidthHighGuard.bounded_fallback q hq
  refine ⟨constant q cutoff,by unfold constant; omega,?_⟩
  intro v hp
  have h := rounded_bound q cutoff v.width hq (fun n hn => (hcut n hn).2.le)
  exact h.trans (Nat.mul_le_mul_left _ (volume_lower q hq v hp))

end
end IntegerMultBounds.Machine.ArbitraryWidthHighMetadataBudget
