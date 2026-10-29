module

public import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Explicit locality depth

The rounded-matrix contraction loses at most one bit every 16p layers.
No ambient line length enters the contraction estimate.
-/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

/-- One block of 16p layers halves the discrepancy bound. -/
theorem locality_block (p : ℕ) (hp : 0 < p) :
    (1-1/(16*(p : ℝ)))^(16*p) ≤ (1/2 : ℝ) := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hnonneg : (0 : ℝ) ≤ 1-1/(16*(p : ℝ)) := by
    have h := (div_le_one (by positivity : (0 : ℝ) < 16*p)).mpr
      (by linarith : (1 : ℝ) ≤ 16*p)
    linarith
  have hbase : 1-1/(16*(p : ℝ)) ≤ Real.exp (-1/(16*(p : ℝ))) := by
    have h := Real.add_one_le_exp (-1/(16*(p : ℝ)))
    simp only [neg_div] at h ⊢
    linarith
  have hpow := pow_le_pow_left₀ hnonneg hbase (16*p)
  rw [← Real.exp_nat_mul] at hpow
  have he : ((16*p : ℕ) : ℝ)*(-1/(16*(p : ℝ))) = -1 := by
    push_cast
    field_simp
  rw [he] at hpow
  apply hpow.trans
  rw [Real.exp_neg]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp 1
    linarith
  simpa only [one_div] using (inv_le_inv₀ (Real.exp_pos 1) (by norm_num : (0 : ℝ) < 2)).mpr htwo

/-- Each block buys one bit; the layer count is explicit and computable. -/
theorem locality_blocks (p k : ℕ) (hp : 0 < p) :
    (1-1/(16*(p : ℝ)))^(16*p*k) ≤ 1/(2 : ℝ)^k := by
  rw [pow_mul]
  have hn : (0 : ℝ) ≤ (1-1/(16*(p : ℝ)))^(16*p) :=
    pow_nonneg (by
      have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
      have h := (div_le_one (by positivity : (0 : ℝ) < 16*p)).mpr
        (by linarith : (1 : ℝ) ≤ 16*p)
      linarith) _
  simpa only [div_pow,one_pow] using pow_le_pow_left₀ hn (locality_block p hp) k

/-- Extra p+4 bits absorb the solution-size bound 16p for RHS bounded by one. -/
def localityDepth (p target : ℕ) : ℕ := 16*p*(target+(p+4))

theorem locality_precision (p target : ℕ) (hp : 0 < p) :
    (1-1/(16*(p : ℝ)))^(localityDepth p target) * (16*p) ≤ 1/(2 : ℝ)^target := by
  have hpR : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hsize : (16 : ℝ)*p ≤ 2^(p+4) := by
    have hpow : (p : ℝ) ≤ 2^p := by exact_mod_cast (show p < 2^p from Nat.lt_two_pow_self).le
    rw [pow_add]
    norm_num
    linarith
  have h := mul_le_mul_of_nonneg_right (locality_blocks p (target+(p+4)) hp)
    (show (0 : ℝ) ≤ 16*p by positivity)
  apply h.trans
  rw [one_div, inv_mul_eq_div, pow_add]
  apply (div_le_iff₀ (by positivity)).mpr
  calc
    (16 : ℝ)*p ≤ 2^(p+4) := hsize
    _ = 1/2^target*(2^target*2^(p+4)) := by field_simp

end IntegerMultBounds.NLogN.PhaseCellMatrix
