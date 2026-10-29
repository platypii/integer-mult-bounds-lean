module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySolutionField
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGuardedCouplingField
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoverySizing
public import IntegerMultBounds.NLogN.PhaseCellCouplingMass
public import IntegerMultBounds.NLogN.SchurRecoveryError

/-! Numerical recovery depends on the boundary field's accuracy, not on how its
words were scattered. Apply the same row estimate and Schur stability once. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

noncomputable def haloRecoveryRhsError (p u q rhsExp : ℕ) (ε : ℝ) : ℝ :=
  (2*PhaseCellBand.width p u+1)*(2/(2 : ℝ)^q)+
    (2*PhaseCellBand.width p u+1)*((2 : ℝ)^stableInteriorExponent p rhsExp*(1/(2 : ℝ)^q))+2*ε

/-- The actual guarded RHS has the recovery magnitude, fits the shared words,
and approximates the exact interior RHS with the usual row error. -/
theorem haloRecoveryRhs_spec {s t p u q w rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
    (hbudget : α^2*d ≤ p) (hb : b ≤ s)
    (hformat : q+recoveryRhsExponent p rhsExp (stableInteriorExponent p rhsExp)
      (couplingCountExponent p u)+2 ≤ w)
    (C : ZMod s → GaussianInt) (hC : ∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^rhsExp)
    (solution : List GaussianInt) (x : ZMod s → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hmag : ∀ i < (haloBoundary s t (PhaseCellBand.width p u) a b).card,
      ‖value q (solution.getD i 0)‖ ≤ (2 : ℝ)^stableInteriorExponent p rhsExp)
    (herror : ∀ i < (haloBoundary s t (PhaseCellBand.width p u) a b).card,
      ‖value q (solution.getD i 0)-(x (bFoldAt s (haloBoundary s t (PhaseCellBand.width p u) a b) i) : ℂ)‖ ≤ ε) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let Y := boundarySolutionField B solution
    let R := guardedCouplingRowField (2^15*p) q t u (PhaseCellBand.width p u) a b true Y C
    (∀ i, ‖value q (R i)‖ ≤ (2 : ℝ)^recoveryRhsExponent p rhsExp
      (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) ∧
    (∀ i, Fits w (R i)) ∧
    ∀ i, |(value q (R i)).re-((value q (C i)).re-
      SchurDominance.couple (realMatrix s t p u) B x i)| ≤ haloRecoveryRhsError p u q rhsExp ε := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let Y := boundarySolutionField B solution
  let R := guardedCouplingRowField (2^15*p) q t u (PhaseCellBand.width p u) a b true Y C
  have hY := boundarySolutionField_magnitude q (stableInteriorExponent p rhsExp) B solution hmag
  have hYerror := boundarySolutionField_error q B solution x ε herror
  have hp0 : 0 < p := by omega
  have hθ0 : 0 < (t : ℝ)/s-1 := lt_of_lt_of_le (by positivity) hθ
  have hcount := couplingCountExponent_spec p u
  have hnorm (i : ZMod s) : ‖value q (R i)‖ ≤ (2 : ℝ)^recoveryRhsExponent p rhsExp
      (stableInteriorExponent p rhsExp) (couplingCountExponent p u) :=
    guardedCouplingRowField_norm true hp0 hst hαu hθ0 hgap hbudget Y C hcount hC (fun i _ => hY i) i
  refine ⟨hnorm,(fun i => fits_of_value_power hformat (R i) (hnorm i)),?_⟩
  have hmass := couplingOffsets_mass_le_two hst hα p u hp hwidth hαu hθ hgap hbudget
  intro i
  have hh := guardedCouplingRowField_error (A := 96) true (by decide) hp0 hst hαu hθ0 hgap hbudget
    hformat Y C x (fun j => (value q (C j)).re) 2 ε 0 hε hcount hC
    (fun j _ => hY j) hYerror hmass (by intro j; simp) hb i (Or.inl rfl)
  simpa only [R,Y,B,haloRecoveryRhsError,Bool.true_eq_false,ite_true,add_zero] using hh

/-- Any accurate interior solve of the computed recovery RHS approximates the
original halo solution. This lemma is independent of the cell schedule. -/
theorem haloRecovery_interior_error {s t p u q a b : ℕ} [NeZero s]
    (hp : 0 < p) (C R D : ZMod s → GaussianInt) (x xI : ZMod s → ℝ) (δ η : ℝ)
    (hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))))
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x
      (fun i => (value q (C i)).re))
    (hxI : SchurDominance.Solves (realMatrix s t p u)
      (haloInterior s t (PhaseCellBand.width p u) a b) xI (fun i => (value q (R i)).re))
    (hR : ∀ i ∈ haloInterior s t (PhaseCellBand.width p u) a b,
      |(value q (R i)).re-((value q (C i)).re-SchurDominance.couple (realMatrix s t p u)
        (haloBoundary s t (PhaseCellBand.width p u) a b) x i)| ≤ δ)
    (hD : PhaseCellInterface.ErrorOn (haloInterior s t (PhaseCellBand.width p u) a b)
      (fun i => (value q (D i)).re) xI η) :
    PhaseCellInterface.ErrorOn (haloInterior s t (PhaseCellBand.width p u) a b)
      (fun i => (value q (D i)).re) x (η+8*p*δ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hμ : (0 : ℝ) < 1/(8*(p : ℝ)) := by positivity
  have hfull : SchurDominance.Solves (realMatrix s t p u)
      (haloInterior s t (PhaseCellBand.width p u) a b ∪ haloBoundary s t (PhaseCellBand.width p u) a b)
      x (fun i => (value q (C i)).re) := by
    rw [haloInterior_union_boundary]
    exact hx
  have hs := SchurDominance.recovery_solves_error _ _ _ (haloInterior_disjoint_boundary s t _ a b)
    _ hμ (SchurDominance.dominates_mono _ Finset.univ _ _ (Finset.subset_univ _) hdom)
    x (fun i => (value q (C i)).re) xI (fun i => (value q (R i)).re) hfull hxI δ hR
  intro i hi
  have hh := hs i hi
  rw [div_div_eq_mul_div,div_one] at hh
  have hd := hD i hi
  rw [Real.norm_eq_abs] at hd ⊢
  have ht := abs_add_le ((value q (D i)).re-xI i) (xI i-x i)
  rw [sub_add_sub_cancel] at ht
  nlinarith only [hh,hd,ht]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
