import IntegerMultBounds.Machine.ActiveRepairLayoutDensity

/-! The manuscript's dyadic radix choice pays full-address repair width. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutDensityArithmetic
open VaryingControlRepairDensity

 theorem late_rewrite (q b n : ℕ) (hbq : b≤q) :
    lateDensity q b n=2*n/(2:ℝ)^b+8*n/(2:ℝ)^(q-b) := by
  unfold lateDensity
  have hq : q=b+(q-b) := by omega
  rw [hq,pow_add]
  have h : (b+(q-b))-b=q-b := by omega
  rw [h]
  field_simp

 theorem early_le_late (q b n : ℕ) : earlyDensity q b n≤lateDensity q b n := by
  unfold earlyDensity lateDensity
  have h : (n:ℝ)/(2:ℝ)^b≤2*n/(2:ℝ)^b := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  linarith

 theorem dyadic_late_paid (p : ℝ) (n ell K A : ℕ)
    (hp : 0<p) (hn : (n:ℝ)≤p) (hell : p≤(2:ℝ)^ell)
    (hK : 8*ell+16≤K) (hA : (A:ℝ)+1≤p^3) :
    lateDensity K (4*ell+6) n*(A+1)≤1 := by
  rw [late_rewrite K (4*ell+6) n (by omega)]
  have hd := Compact.uniform_repair_density p n ell K hp hn hell hK
  have hh := mul_le_mul_of_nonneg_right hd (by positivity : (0:ℝ)≤A+1)
  have hc : (5/(128*p^3))*(A+1)≤5/128 := by
    have hpos : 0<p^3 := by positivity
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<128*p^3)).mpr
    nlinarith
  calc
    _ ≤ (5/(128*p^3))*(A+1) := hh
    _ ≤ 5/128 := hc
    _ ≤ 1 := by norm_num

 theorem dyadic_early_paid (p : ℝ) (n ell K A : ℕ)
    (hp : 0<p) (hn : (n:ℝ)≤p) (hell : p≤(2:ℝ)^ell)
    (hK : 8*ell+16≤K) (hA : (A:ℝ)+1≤p^3) :
    earlyDensity K (4*ell+6) n*(A+1)≤1 :=
  (mul_le_mul_of_nonneg_right (early_le_late K (4*ell+6) n) (by positivity)).trans
    (dyadic_late_paid p n ell K A hp hn hell hK hA)

end IntegerMultBounds.Machine.ActiveRepairLayoutDensityArithmetic
