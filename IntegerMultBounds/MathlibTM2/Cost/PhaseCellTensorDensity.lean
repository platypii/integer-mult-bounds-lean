module

public import IntegerMultBounds.NLogN.PhaseCellBand
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Full-period inverse costs aggregate by axis density, with one shared charge
per axis. This calculation keeps exposure and layout costs explicit. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.NLogN

/-- The extra unit in the integer square-root band contributes only a constant. -/
theorem phaseCellBand_sq_le (p u : ℕ) :
    (PhaseCellBand.width p u : ℝ)^2 ≤ 32*(p : ℝ)/u+2 := by
  have hs := Nat.sqrt_le' (16*p/u)
  have hb : (PhaseCellBand.width p u)^2 ≤ 2*(16*p/u)+2 := by
    unfold PhaseCellBand.width
    nlinarith only [hs]
  have hbR : (PhaseCellBand.width p u : ℝ)^2 ≤ 2*((16*p/u : ℕ) : ℝ)+2 := by exact_mod_cast hb
  have hdiv : ((16*p/u : ℕ) : ℝ) ≤ (16*(p : ℝ))/u := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using (Nat.cast_div_le (m := 16*p) (n := u) (α := ℝ))
  calc
    _ ≤ 2*(16*(p : ℝ)/u)+2 := hbR.trans (by linarith only [hdiv])
    _ = _ := by ring

/-- A sequential axis schedule pays shared setup once per axis. Its native
arithmetic density sums to dimension plus squared band, rather than their product. -/
theorem tensorAxisDensityCost_le {d : ℕ} (hd : 0 < d)
    (cost lines axis : Fin d → ℝ) (shared volume D band precision : ℝ)
    (hD : 0 ≤ D) (hprecision : 0 ≤ precision)
    (hvolume : ∀ i, lines i*axis i ≤ volume)
    (hcost : ∀ i, cost i ≤ shared+lines i*D*axis i*(1+band^2/d)*precision) :
    (∑ i, cost i) ≤ (d : ℝ)*shared+D*volume*((d : ℝ)+band^2)*precision := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdensity : 0 ≤ 1+band^2/d := by positivity
  have heach (i : Fin d) : cost i ≤ shared+D*volume*(1+band^2/d)*precision := by
    have hb := mul_le_mul_of_nonneg_right (hvolume i)
      (show 0 ≤ D*(1+band^2/d)*precision by positivity)
    have heq : lines i*D*axis i*(1+band^2/d)*precision =
        (lines i*axis i)*(D*(1+band^2/d)*precision) := by ring
    have hc := hcost i
    rw [heq] at hc
    exact hc.trans (by nlinarith only [hb])
  calc
    (∑ i, cost i) ≤ ∑ _ : Fin d, (shared+D*volume*(1+band^2/d)*precision) :=
      Finset.sum_le_sum (fun i _ => heach i)
    _ = (d : ℝ)*shared+D*volume*((d : ℝ)+band^2)*precision := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      field_simp

/-- Arithmetic comparison for a full-period solve on every axis. This leaves the
movement bill outside the estimate; it cannot justify replacing short-field exposure. -/
theorem fullPeriodTensorCost_le {d : ℕ} (hd : 0 < d) (p u : ℕ)
    (cost lines axis : Fin d → ℝ) (volume D precision : ℝ)
    (hD : 0 ≤ D) (hvolume : 0 ≤ volume) (hprecision : 0 ≤ precision)
    (hlines : ∀ i, lines i*axis i ≤ volume)
    (hcost : ∀ i, cost i ≤ 2624001*volume+410+
      lines i*D*axis i*(1+(PhaseCellBand.width p u : ℝ)^2/d)*precision) :
    (∑ i, cost i) ≤ (d : ℝ)*(2624001*volume+410)+
      D*volume*((d : ℝ)+32*(p : ℝ)/u+2)*precision := by
  have hb := tensorAxisDensityCost_le hd cost lines axis (2624001*volume+410)
    volume D (PhaseCellBand.width p u) precision hD hprecision hlines hcost
  have hw := phaseCellBand_sq_le p u
  have hm := mul_le_mul_of_nonneg_left (add_le_add_left hw (d : ℝ))
    (show 0 ≤ D*volume by positivity)
  have hs := mul_le_mul_of_nonneg_right hm hprecision
  exact hb.trans (by nlinarith only [hs])

end IntegerMultBounds.MathlibTM2.Cost
