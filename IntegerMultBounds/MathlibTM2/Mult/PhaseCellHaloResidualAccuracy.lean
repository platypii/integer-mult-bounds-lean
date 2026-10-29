module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingFieldError
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloResidualNormalization
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellResidualSizing
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryHaloPrecision
public import IntegerMultBounds.NLogN.PhaseCellCouplingMass
public import IntegerMultBounds.NLogN.SchurBlockSolve

/-! The observed real halo residual approximates the exact Schur RHS.
The estimate depends only on the whole-interior error, not its cell schedule. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.SchurDominance

noncomputable def haloResidualError (p u q rhsExp cellTarget : ℕ) : ℝ :=
  (2*PhaseCellBand.width p u+1)*(2/(2 : ℝ)^q)+
    (2*PhaseCellBand.width p u+1)*((2 : ℝ)^stableInteriorExponent p rhsExp*(1/(2 : ℝ)^q))+
      2*(1/(2 : ℝ)^cellTarget)

theorem value_realPartWord_sub_norm (q : ℕ) (z : GaussianInt) (c : ℝ) :
    ‖value q (realPartWord z)-(c : ℂ)‖ = |(value q z).re-c| := by
  have hz : value q (realPartWord z) = ((value q z).re : ℂ) := by
    apply Complex.ext <;> simp only [value,realPartWord,Int.cast_zero,zero_div,Complex.ofReal_re,Complex.ofReal_im]
  rw [hz,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]

theorem haloResidual_error_bound {s t p u q w rhsExp cellTarget a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hst : s < t) (hα : 0 < α) (hwidth : 8*p ≤ 2^u)
    (hαu : α^2 = (u : ℝ)) (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hw : q+couplingRowExponent rhsExp (stableInteriorExponent p rhsExp)
      (8*p+1) (couplingCountExponent p u)+2 ≤ w)
    (hdom : DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))))
    (C D : ZMod s → GaussianInt) (hC : ∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ZMod s → ℝ)
    (hx : Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun i => (value q (C i)).re))
    (herror : PhaseCellInterface.ErrorOn (haloInterior s t (PhaseCellBand.width p u) a b)
      (fun i => (value q (D i)).re) x (1/(2 : ℝ)^cellTarget))
    (R : (ZMod s → ℝ) → ZMod s → ℝ)
    (hR : ∀ c, Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) (R c) c)
    (i : ZMod s) :
    ‖value q (realPartWord (couplingRowField (2^15*p) q t u (PhaseCellBand.width p u) a b false D C i))-
      (residual (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) R
        (fun k => (value q (C k)).re) i : ℂ)‖ ≤ haloResidualError p u q rhsExp cellTarget := by
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hμ : (0 : ℝ) < 1/(8*(p : ℝ)) := by positivity
  have hθpos : 0 < (t : ℝ)/s-1 := lt_of_lt_of_le (by positivity : 0 < 1/(4*(p : ℝ))) hθ
  let I := haloInterior s t (PhaseCellBand.width p u) a b
  let rhs := fun k => (value q (C k)).re
  have hD := stableInterior_norm hp0 I hdom C D hC x hx herror
  have hC' : ∀ k, ‖value q (realPartWord (C k))‖ ≤ (2 : ℝ)^rhsExp := by
    intro k; rw [value_realPartWord_norm]; exact (Complex.abs_re_le_norm _).trans (hC k)
  have hDR : ∀ k ∈ I, |(value q (realPartWord (D k))).re-R rhs k| ≤ 1/(2 : ℝ)^cellTarget := by
    intro k hk
    have he := solves_unique (realMatrix s t p u) I _ hμ
      (dominates_mono _ Finset.univ I _ (Finset.subset_univ I) hdom) x (R rhs) rhs hx (hR rhs) k hk
    rw [← he,value_realPartWord_re]
    simpa only [Real.norm_eq_abs] using herror k hk
  have hh := couplingRowField_error (A := 96) false (by decide) hp0 hst hαu hθpos hgap hbudget hw
    (fun k => realPartWord (D k)) (fun k => realPartWord (C k)) (R rhs) rhs
    2 (1/(2 : ℝ)^cellTarget) 0 (by positivity) (couplingCountExponent_spec p u) hC' hD hDR
    (couplingOffsets_mass_le_two hst hα p u hp hwidth hαu hθ hgap hbudget)
    (by intro k; simp [rhs]) i
  rw [← couplingRowField_realPart] at hh
  rw [value_realPartWord_sub_norm]
  simpa only [value_realPartWord_re,Bool.false_eq_true,ite_false,add_zero,
    haloResidualError,SchurDominance.residual,couple,I,rhs] using hh

theorem haloResidualError_le (p u l cellTarget rhsExp : ℕ) :
    haloResidualError p u (executionPrecision p l cellTarget rhsExp) rhsExp cellTarget ≤
      3/(2 : ℝ)^cellTarget := by
  have hround := initialResidual_roundoff_budget p u l cellTarget rhsExp
  unfold haloResidualError
  apply (add_le_add hround (le_refl (2*(1/(2 : ℝ)^cellTarget)))).trans
  show 1/(2 : ℝ)^cellTarget+2*(1/(2 : ℝ)^cellTarget) ≤ 3/(2 : ℝ)^cellTarget
  exact le_of_eq (by ring)

/-- Residual error pays its own budget; matrix accuracy is handled separately. -/
theorem haloResidual_budget_of_target (p u l target rhsExp cellTarget : ℕ)
    (haccuracy : initialSchurTarget p u target rhsExp ≤ cellTarget) :
    32*(p : ℝ)*haloResidualError p u (executionPrecision p l cellTarget rhsExp) rhsExp cellTarget ≤
      1/(2 : ℝ)^(target+1) := by
  have hcoeff : 96*(p : ℝ) ≤ (2 : ℝ)^(8*p+4) := by
    have hpPow : 8*(p : ℝ) ≤ (2 : ℝ)^(8*p) := by
      exact_mod_cast (Nat.lt_two_pow_self (n := 8*p)).le
    calc
      _ ≤ 16*(2 : ℝ)^(8*p) := by nlinarith [Nat.cast_nonneg (α := ℝ) p]
      _ = _ := by rw [pow_add]; norm_num; ring
  have hbits : (8*p+4)+(target+1) ≤ cellTarget := by
    unfold initialSchurTarget at haccuracy
    rw [recoveryFirstTarget_canonical] at haccuracy
    unfold recoveryTarget recoveryGuardBits at haccuracy
    omega
  calc
    _ ≤ 32*(p : ℝ)*(3/(2 : ℝ)^cellTarget) :=
      mul_le_mul_of_nonneg_left (haloResidualError_le p u l cellTarget rhsExp) (by positivity)
    _ = 96*(p : ℝ)/(2 : ℝ)^cellTarget := by ring
    _ ≤ 1/(2 : ℝ)^(target+1) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      calc
        _ ≤ (2 : ℝ)^(8*p+4)*(2 : ℝ)^(target+1) :=
          mul_le_mul_of_nonneg_right hcoeff (by positivity)
        _ ≤ 1*(2 : ℝ)^cellTarget := by
          rw [← pow_add,one_mul]
          exact pow_le_pow_right₀ (by norm_num) hbits

theorem boundaryHaloTarget_residual_budget (p u l target rhsExp rowCount : ℕ) :
    let cellTarget := boundaryHaloTarget p u target rhsExp rowCount
    let q := executionPrecision p l (initialSchurTarget p u
      (boundaryTableBits p target rhsExp rowCount) 2) 2
    32*(p : ℝ)*haloResidualError p u q rhsExp cellTarget ≤ 1/(2 : ℝ)^(target+1) := by
  have h := haloResidual_budget_of_target p u l target rhsExp _
    (boundaryHaloTarget_accuracy p u target rhsExp rowCount)
  simpa only [(boundaryHaloTarget_sizing p u l target rhsExp rowCount).1] using h

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
