module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellTensorDensity
public import IntegerMultBounds.MathlibTM2.Mult.Moduli
public import IntegerMultBounds.MathlibTM2.Mult.Sizes
import Mathlib.Tactic.Linarith

/-! Actual source-tensor line multiplicities fit the selected target volume.
Reuse the established axis-density sum, with both real components accounted. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult
open scoped BigOperators

def sourceTensorLineCount (n : ℕ) (i : Fin (Sizes.d n)) : ℕ :=
  ∏ j ∈ Finset.univ.erase i, Sizes.s n j

theorem sourceTensorLineCount_pos (n : ℕ) (i : Fin (Sizes.d n)) :
    0 < sourceTensorLineCount n i := by
  apply Finset.prod_pos
  intro j hj
  exact (Sizes.srcLen_prime n j.val).pos

theorem selectedSourceTensorLineVolume_le {n : ℕ} (h : Sizes.Big n) (i : Fin (Sizes.d n)) :
    sourceTensorLineCount n i*Sizes.t n i ≤ Sizes.T n := by
  have hp : sourceTensorLineCount n i ≤ ∏ j ∈ Finset.univ.erase i, Sizes.t n j := by
    apply Finset.prod_le_prod
    intro j hj
    exact (h.good.lt j).le
  calc
    _ ≤ (∏ j ∈ Finset.univ.erase i, Sizes.t n j)*Sizes.t n i := Nat.mul_le_mul_right _ hp
    _ = ∏ j, Sizes.t n j := Finset.prod_erase_mul _ _ (Finset.mem_univ i)
    _ = Sizes.T n := Sizes.prod_t h.one_le_d

/-- Two real component archives plus the fixed unit in the fitting bound cost
at most three source-line volumes. No axis/prefix multiplicity is supplied. -/
theorem selectedCyclicComponentLineVolume_le {n : ℕ} (h : Sizes.Big n) (i : Fin (Sizes.d n)) :
    (2*sourceTensorLineCount n i+1)*Sizes.t n i ≤ 3*Sizes.T n := by
  have hp := sourceTensorLineCount_pos n i
  have hv := selectedSourceTensorLineVolume_le h i
  have hm := Nat.mul_le_mul_right (Sizes.t n i)
    (show 2*sourceTensorLineCount n i+1 ≤ 3*sourceTensorLineCount n i by omega)
  nlinarith only [hm,hv]

/-- Aggregate the fitting numerical schedule over the actual tensor axes.
This is cost composition; it does not supply missing tensor routing executions. -/
theorem selectedFittingCyclicTensorDensity_le {n : ℕ} (h : Sizes.Big n) (u : ℕ)
    (cost : Fin (Sizes.d n) → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hcost : ∀ i, cost i ≤ 10*(Sizes.T n : ℝ)+
      2*A*((2*sourceTensorLineCount n i+1 : ℕ) : ℝ)*(Sizes.t n i : ℝ)*
        (1+(PhaseCellBand.width (Sizes.p n) u : ℝ)^2/Sizes.d n)*(Sizes.p n : ℝ)^(129/128 : ℝ)) :
    (∑ i, cost i) ≤ 10*(Sizes.d n : ℝ)*Sizes.T n+
      6*A*Sizes.T n*((Sizes.d n : ℝ)+32*(Sizes.p n : ℝ)/u+2)*
        (Sizes.p n : ℝ)^(129/128 : ℝ) := by
  have hd : 0 < Sizes.d n := by have := h.one_le_d; omega
  have hv (i : Fin (Sizes.d n)) :
      (((2*sourceTensorLineCount n i+1 : ℕ) : ℝ)*(Sizes.t n i : ℝ)) ≤ 3*Sizes.T n := by
    exact_mod_cast selectedCyclicComponentLineVolume_le h i
  have hs := tensorAxisDensityCost_le hd cost
    (fun i => ((2*sourceTensorLineCount n i+1 : ℕ) : ℝ)) (fun i => (Sizes.t n i : ℝ))
    (10*(Sizes.T n : ℝ)) (3*(Sizes.T n : ℝ)) (2*A)
    (PhaseCellBand.width (Sizes.p n) u) ((Sizes.p n : ℝ)^(129/128 : ℝ))
    (by positivity) (by positivity) hv (by intro i; nlinarith only [hcost i])
  have hb := phaseCellBand_sq_le (Sizes.p n) u
  have hm := mul_le_mul_of_nonneg_left hb
    (by positivity : (0 : ℝ) ≤ 6*A*Sizes.T n*(Sizes.p n : ℝ)^(129/128 : ℝ))
  nlinarith only [hs,hm]

end IntegerMultBounds.MathlibTM2.Cost
