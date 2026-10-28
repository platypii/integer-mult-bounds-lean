module

public import IntegerMultBounds.MathlibTM2.Mult.Moduli
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Axis density, independent of the inverse implementation. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult

theorem axisGap_mul_dimension_le {d s t : ℕ} (hst : s ≤ t)
    (haxis : Moduli.AxisBounds d s t) : d*(t-s) ≤ t := by
  have hsum : s+(t-s) = t := Nat.add_sub_of_le hst
  have h := haxis.lower
  nlinarith only [h,hsum,Nat.zero_le (d*(t-s))]

theorem axisGapVolume_le {d s t band : ℕ} (hd : 0 < d) (hst : s ≤ t)
    (haxis : Moduli.AxisBounds d s t) :
    ((t+(t-s)*band^2 : ℕ) : ℝ) ≤ (t : ℝ)*(1+(band : ℝ)^2/d) := by
  have hgap : (d : ℝ)*(t-s : ℕ) ≤ t := by
    exact_mod_cast axisGap_mul_dimension_le hst haxis
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hquot : ((t-s : ℕ) : ℝ) ≤ (t : ℝ)/d :=
    (le_div_iff₀ hd').2 (by nlinarith only [hgap])
  have hscaled := mul_le_mul_of_nonneg_right hquot (sq_nonneg (band : ℝ))
  push_cast
  calc
    (t : ℝ)+(t-s : ℕ)*(band : ℝ)^2 ≤ (t : ℝ)+((t : ℝ)/d)*(band : ℝ)^2 := by
      linarith only [hscaled]
    _ = (t : ℝ)*(1+(band : ℝ)^2/d) := by ring

end IntegerMultBounds.MathlibTM2.Cost
