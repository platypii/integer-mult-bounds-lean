module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryHaloRecoveryPrecision
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloRecoveryAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInterval

/-! At the actual retained boundary format, the second interior solve needs
only its usual accuracy contract to recover the full halo to the final target. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem haloRecovery_boundary_format_spec (p u l target rhsExp a b : ℕ)
    {s t : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
    (hbudget : α^2*d ≤ p) (hb : b ≤ s)
    (hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ)))) :
    let band := PhaseCellBand.width p u
    let B := haloBoundary s t band a b
    let solveTarget := boundaryRecoveryTarget p target
    let T := initialSchurTarget p u (boundaryTableBits p solveTarget rhsExp B.card) 2
    let q := executionPrecision p l T 2
    let w := executionWidth p l T 2
    let k := boundaryHaloRecoveryTarget p solveTarget B.card
    let e := recoveryRhsExponent p rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)
    ∀ (C : ZMod s → GaussianInt) (solution : List GaussianInt) (x : ZMod s → ℝ),
      (∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^rhsExp) →
      (∀ i < B.card, ‖value q (solution.getD i 0)-(x (bFoldAt s B i) : ℂ)‖ ≤ 3/(2 : ℝ)^solveTarget ∧
        ‖value q (solution.getD i 0)‖ ≤ (2 : ℝ)^stableInteriorExponent p rhsExp) →
      SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x (fun i => (value q (C i)).re) →
      let Y := boundarySolutionField B solution
      let R := guardedCouplingRowField (2^15*p) q t u band a b true Y C
      (∀ i, ‖value q (R i)‖ ≤ (2 : ℝ)^e) ∧ (∀ i, Fits w (R i)) ∧
      ∃ xI : ZMod s → ℝ,
        SchurDominance.Solves (realMatrix s t p u) (haloInterior s t band a b) xI (fun i => (value q (R i)).re) ∧
        ∀ (D : ZMod s → GaussianInt),
          PhaseCellInterface.ErrorOn (haloInterior s t band a b) (fun i => (value q (D i)).re) xI (1/(2 : ℝ)^k) →
          PhaseCellInterface.ErrorOn (haloVertices s a b)
            (fun i => if i ∈ haloInterior s t band a b then (value q (D i)).re else (value q (Y i)).re)
            x (1/(2 : ℝ)^target) := by
  dsimp only
  intro C solution x hC hsolution hx
  let band := PhaseCellBand.width p u
  let B := haloBoundary s t band a b
  let solveTarget := boundaryRecoveryTarget p target
  let T := initialSchurTarget p u (boundaryTableBits p solveTarget rhsExp B.card) 2
  let q := executionPrecision p l T 2
  let w := executionWidth p l T 2
  let k := boundaryHaloRecoveryTarget p solveTarget B.card
  let ε : ℝ := 3/(2 : ℝ)^solveTarget
  let Y := boundarySolutionField B solution
  let R := guardedCouplingRowField (2^15*p) q t u band a b true Y C
  have hformat := (boundaryHaloRecovery_format p u l solveTarget rhsExp B.card).1
  have hr := haloRecoveryRhs_spec hp hwidth hα hst hαu hθ hgap hbudget hb hformat C hC
    solution x ε (by dsimp [ε]; positivity) (fun i hi => (hsolution i hi).2) (fun i hi => (hsolution i hi).1)
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hμ : (0 : ℝ) < 1/(8*(p : ℝ)) := by positivity
  obtain ⟨xI,hxI⟩ := SchurDominance.solves_exists (realMatrix s t p u) (haloInterior s t band a b)
    _ hμ (SchurDominance.dominates_mono _ Finset.univ _ _ (Finset.subset_univ _) hdom)
    (fun i => (value q (R i)).re)
  refine ⟨hr.1,hr.2.1,xI,hxI,?_⟩
  intro D hD
  have hcore := haloRecovery_interior_error hp0 C R D x xI (haloRecoveryRhsError p u q rhsExp ε)
    (1/(2 : ℝ)^k) hdom hx hxI (fun i _ => hr.2.2 i) hD
  have hboundary : PhaseCellInterface.ErrorOn B (fun i => (value q (Y i)).re) x ε := by
    intro i hi
    simpa only [Real.norm_eq_abs] using boundarySolutionField_error q B solution x ε
      (fun j hj => (hsolution j hj).1) i hi
  have hfinal := hcore.union_ite hboundary
  rw [haloInterior_union_boundary] at hfinal
  have hpay : max (1/(2 : ℝ)^k+8*p*haloRecoveryRhsError p u q rhsExp ε) ε ≤ 1/(2 : ℝ)^target := by
    simpa only [k,q,T,solveTarget,ε,haloRecoveryRhsError] using
      boundaryHaloRecovery_error_budget p u l target rhsExp B.card
  intro i hi
  exact (hfinal i hi).trans hpay

/-- The retained boundary buffer already satisfies the second interior solver's
initial encoded-range contract; no normalization or extra tape is needed. -/
theorem haloRecovery_boundary_range {s : ℕ} [NeZero s] (A p u l k rhsExp q w a N : ℕ)
    (B : Finset (ZMod s)) (solution : List GaussianInt)
    (hmag : ∀ i < B.card, ‖value q (solution.getD i 0)‖ ≤ (2 : ℝ)^stableInteriorExponent p rhsExp) :
    EncodedRange A w q (interiorOutputExponent p l k
      (recoveryRhsExponent p rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)))
      (cstream A w (packedInterval a N (boundarySolutionField B solution))) := by
  have hn := boundarySolutionField_magnitude q (stableInteriorExponent p rhsExp) B solution hmag
  have he : stableInteriorExponent p rhsExp ≤
      recoveryRhsExponent p rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u) := by
    unfold recoveryRhsExponent couplingRowExponent
    omega
  have hbound := he.trans (rhsExponent_le_interiorOutputExponent p l k _)
  refine ⟨packedInterval a N (boundarySolutionField B solution),rfl,?_⟩
  intro z hz
  have hz' : z ∈ chirpLine s (boundarySolutionField B solution) :=
    List.mem_of_mem_drop (List.mem_of_mem_take hz)
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hz'
  exact (hn _).trans (pow_le_pow_right₀ (by norm_num) hbound)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
