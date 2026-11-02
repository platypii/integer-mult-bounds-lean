module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellDyadicTransposeCharge

/-! The generated canonical schedule has the same full-width/remainder charge
as the split construction. No equality of indexed plan objects is needed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

private theorem canonicalCharge_congr (fuel a a' b W : ℕ) (ha : a = a')
    (h : a+b ≤ fuel) (h' : a'+b ≤ fuel) (f : ℕ → ℝ) :
    (dyadicTransposePlan fuel a b W h).weightedCharge f =
      (dyadicTransposePlan fuel a' b W h').weightedCharge f := by
  subst a'
  rfl

theorem dyadicTransposePlan_splitCharge_le (q r b W fuel : ℕ) (hb : 0 < b)
    (h : q*b+r+b ≤ fuel) (f : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k : ℕ, 0 < k → f k ≤ C*k) :
    (dyadicTransposePlan fuel (q*b+r) b W h).weightedCharge f ≤
      q*f b+C*(r+b : ℕ) := by
  induction q generalizing W fuel with
  | zero =>
    simpa only [Nat.zero_mul,Nat.zero_add,Nat.cast_zero,zero_mul,zero_add] using
      (dyadicTransposePlan fuel (0*b+r) b W h).weightedCharge_le_linear f C hC hf
  | succ q ih =>
    have hmul : (q+1)*b = q*b+b := Nat.succ_mul q b
    cases fuel with
    | zero => omega
    | succ fuel =>
      have ha : (q+1)*b+r ≠ 0 := by omega
      have hb0 : b ≠ 0 := by omega
      have hba : b ≤ (q+1)*b+r := by omega
      have he : (q+1)*b+r-b = q*b+r := by omega
      have hh := ih (2^b*W) fuel (by omega)
      simp only [dyadicTransposePlan,ha,hb0,↓reduceDIte,hba,
        DyadicTransposePlan.weightedCharge_cast,DyadicTransposePlan.weightedCharge]
      rw [canonicalCharge_congr fuel _ (q*b+r) b (2^b*W) he _ (by omega) f]
      simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul,
        add_assoc,add_comm,add_left_comm] using add_le_add_left hh (f b)

theorem dyadicTransposePlan_rpowCharge_le (fuel a b W : ℕ) (hb : 0 < b)
    (h : a+b ≤ fuel) (τ : ℝ) (hτ : τ ≤ 1) :
    (dyadicTransposePlan fuel a b W h).weightedCharge (fun k => (k : ℝ)^τ+1) ≤
      (a : ℝ)/b*((b : ℝ)^τ+1)+4*b := by
  have hdecomp : a/b*b+a%b = a := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod a b
  have hh := dyadicTransposePlan_splitCharge_le (a/b) (a%b) b W fuel hb
    (by omega) (fun k => (k : ℝ)^τ+1) 2 (by norm_num) (by
      intro k hk
      have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hp := Real.rpow_le_rpow_of_exponent_le hkR hτ
      rw [Real.rpow_one] at hp
      linarith)
  have hh' : (dyadicTransposePlan fuel a b W h).weightedCharge (fun k => (k : ℝ)^τ+1) ≤
      (a/b : ℕ)*((b : ℝ)^τ+1)+2*(a%b+b : ℕ) := by
    rw [canonicalCharge_congr fuel _ a b W hdecomp _ h] at hh
    exact hh
  have hq : ((a/b : ℕ) : ℝ) ≤ (a : ℝ)/b := by
    apply (le_div_iff₀ (by exact_mod_cast hb : (0 : ℝ) < b)).2
    exact_mod_cast Nat.div_mul_le_self a b
  have hm := mul_le_mul_of_nonneg_right hq (by positivity : 0 ≤ (b : ℝ)^τ+1)
  have hr : ((a%b : ℕ) : ℝ) ≤ b := by exact_mod_cast (Nat.mod_lt a hb).le
  push_cast at hh'
  linarith

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
