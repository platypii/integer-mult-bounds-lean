module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGuardedCouplingRowValue

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloInteriorAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryNormalizationBudget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupportBudget

/-! Cell accuracy and stability supply the existing boundary normalization
kernel's magnitude contract for the actual real projected residual words. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry ScalarPlacement

theorem haloResidual_norm_bound
    {s t p u q rhsExp cellTarget : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hαu : α^2 = (u : ℝ)) (hθ : 0 < (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (a b : ℕ)
    (hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))))
    (C D : ZMod s → GaussianInt) (hC : ∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun i => (value q (C i)).re))
    (herror : PhaseCellInterface.ErrorOn (haloInterior s t (PhaseCellBand.width p u) a b)
      (fun i => (value q (D i)).re) x (1/(2 : ℝ)^cellTarget))
    (i : ZMod s) :
    ‖value q (realPartWord (couplingRowField (2^15*p) q t u
      (PhaseCellBand.width p u) a b false D C i))‖ ≤
      (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp)
        (8*p+1) (couplingCountExponent p u) := by
  have hD := stableInterior_norm hp _ hdom C D hC x hx herror
  have hC' : ∀ j, ‖value q (realPartWord (C j))‖ ≤ (2 : ℝ)^rhsExp := by
    intro j
    rw [value_realPartWord_norm]
    exact (Complex.abs_re_le_norm _).trans (hC j)
  rw [couplingRowField_realPart]
  exact couplingRowField_norm false hp hst hαu hθ hgap hbudget
    (fun j => realPartWord (D j)) (fun j => realPartWord (C j))
    (couplingCountExponent_spec p u) hC' hD i

theorem haloResidual_normalization_bound
    {s t p u q rhsExp cellTarget : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hαu : α^2 = (u : ℝ)) (hθ : 0 < (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (a b l target : ℕ)
    (hq : q = executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target rhsExp
      (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)
    (hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))))
    (C D : ZMod s → GaussianInt) (hC : ∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun i => (value q (C i)).re))
    (herror : PhaseCellInterface.ErrorOn (haloInterior s t (PhaseCellBand.width p u) a b)
      (fun i => (value q (D i)).re) x (1/(2 : ℝ)^cellTarget))
    (i : ZMod s) :
    let z := realPartWord (couplingRowField (2^15*p) q t u (PhaseCellBand.width p u) a b false D C i)
    (|gv q z.re| ≤ (2 : ℝ)^(q/2) ∧ |gv q z.im| ≤ (2 : ℝ)^(q/2)) ∧
      (|gv q (normalizeBoundaryWord q (q/2-1) z).re| ≤ 1/2 ∧
        |gv q (normalizeBoundaryWord q (q/2-1) z).im| ≤ 1/2) := by
  dsimp only
  let z := realPartWord (couplingRowField (2^15*p) q t u (PhaseCellBand.width p u) a b false D C i)
  have hnorm := haloResidual_norm_bound hp hst hαu hθ hgap hbudget a b hdom C D hC x hx herror i
  have hbound : |gv q z.re| ≤ (2 : ℝ)^(q/2) ∧ |gv q z.im| ≤ (2 : ℝ)^(q/2) := by
    have hz := boundary_residual_normalization_bound p u l target rhsExp
      (haloBoundary s t (PhaseCellBand.width p u) a b).card z
      (by simpa only [value,gv,← hq] using (And.intro
        ((Complex.abs_re_le_norm (value q z)).trans hnorm)
        ((Complex.abs_im_le_norm (value q z)).trans hnorm)))
    simpa only [← hq] using hz
  have hprecision := boundary_normalization_precision p u l target rhsExp
    (haloBoundary s t (PhaseCellBand.width p u) a b).card
  dsimp only at hprecision
  rw [← hq] at hprecision
  refine ⟨hbound,normalizeBoundaryWord_bound q (q/2) (q/2-1) (by omega) z hbound⟩

theorem haloResidual_normalization_bound_of_cells
    {s t p u q rhsExp cellTarget : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hαu : α^2 = (u : ℝ)) (hθ : 0 < (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (a b l target : ℕ)
    (hq : q = executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target rhsExp
      (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)
    (hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))))
    (C D : ZMod s → GaussianInt) (hC : ∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun i => (value q (C i)).re))
    (hcell : ∀ phase ∈ haloCellPhases s t (PhaseCellBand.width p u) a b,
      ∀ i < haloLength s t (PhaseCellBand.width p u) a b phase,
      |(value q (D ((haloStart s t (PhaseCellBand.width p u) a phase : ZMod s)+(i : ZMod s)))).re-
        x ((haloStart s t (PhaseCellBand.width p u) a phase : ZMod s)+(i : ZMod s))| ≤ 1/(2 : ℝ)^cellTarget)
    (i : ZMod s) :
    let z := realPartWord (couplingRowField (2^15*p) q t u (PhaseCellBand.width p u) a b false D C i)
    (|gv q z.re| ≤ (2 : ℝ)^(q/2) ∧ |gv q z.im| ≤ (2 : ℝ)^(q/2)) ∧
      (|gv q (normalizeBoundaryWord q (q/2-1) z).re| ≤ 1/2 ∧
        |gv q (normalizeBoundaryWord q (q/2-1) z).im| ≤ 1/2) := by
  exact haloResidual_normalization_bound hp hst hαu hθ hgap hbudget a b l target hq hdom C D hC x hx
    (haloInterior_error_of_cells hst _ a b _ x _ hcell) i

theorem haloResidual_guarded_normalization_bound
    {s t p u q rhsExp cellTarget : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hαu : α^2 = (u : ℝ)) (hθ : 0 < (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (a b l target : ℕ) (hb : b ≤ s)
    (hq : q = executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target rhsExp
      (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)
    (hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))))
    (C D : ZMod s → GaussianInt) (hC : ∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun i => (value q (C i)).re))
    (herror : PhaseCellInterface.ErrorOn (haloInterior s t (PhaseCellBand.width p u) a b)
      (fun i => (value q (D i)).re) x (1/(2 : ℝ)^cellTarget))
    (i : ZMod s) (hi : i ∈ haloBoundary s t (PhaseCellBand.width p u) a b) :
    let z := realPartWord (guardedCouplingRowField (2^15*p) q t u (PhaseCellBand.width p u) a b false D C i)
    (|gv q z.re| ≤ (2 : ℝ)^(q/2) ∧ |gv q z.im| ≤ (2 : ℝ)^(q/2)) ∧
      (|gv q (normalizeBoundaryWord q (q/2-1) z).re| ≤ 1/2 ∧
        |gv q (normalizeBoundaryWord q (q/2-1) z).im| ≤ 1/2) := by
  simpa only [guardedCouplingRowField_eq hst (2^15*p) q u (PhaseCellBand.width p u) a b false hb D C i (Or.inr hi)]
    using haloResidual_normalization_bound hp hst hαu hθ hgap hbudget a b l target hq hdom C D hC x hx herror i

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
