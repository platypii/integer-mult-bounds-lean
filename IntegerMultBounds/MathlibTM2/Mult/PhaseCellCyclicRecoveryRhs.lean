module

public import IntegerMultBounds.NLogN.PhaseCellCyclicRecoveryPieces
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloRecoveryAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTargetOwnedRecoveryJob

/-! Both physical recovery passes read the one computed cyclic boundary field. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem cyclicRecoveryRhs_spec {s t p u l q w a n : ℕ} [NeZero s] {alpha gap : ℝ}
    (axis : RecoveryAxisBounds s t p u l alpha gap) (ha : a < s) (hn : n ≤ s)
    (hw : q+recoveryRhsExponent p 2 (stableInteriorExponent p 2)
      (couplingCountExponent p u)+2 ≤ w)
    (C : ZMod s → GaussianInt) (hC : ∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^2)
    (solution : List GaussianInt) (x : ZMod s → ℝ) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hmag : ∀ i < (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card,
      ‖value q (solution.getD i 0)‖ ≤ (2 : ℝ)^stableInteriorExponent p 2)
    (herror : ∀ i < (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card,
      ‖value q (solution.getD i 0)-(x (bFoldAt s (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n) i) : ℂ)‖ ≤ epsilon) :
    let band := PhaseCellBand.width p u
    let B := cyclicPrincipalBoundary s t band a n
    let Y := boundarySolutionField B solution
    let R := fun i => if i ∈ haloInterior s t band a (a+min n (s-a)) then
      guardedCouplingRowField (2^15*p) q t u band a (a+min n (s-a)) true Y C i else
      guardedCouplingRowField (2^15*p) q t u band 0 (n-min n (s-a)) true Y C i
    ∀ i ∈ cyclicPrincipalInterior s t band a n,
      ‖value q (R i)‖ ≤ (2 : ℝ)^recoveryRhsExponent p 2
        (stableInteriorExponent p 2) (couplingCountExponent p u) ∧
      Fits w (R i) ∧
      |(value q (R i)).re-((value q (C i)).re-SchurDominance.couple (realMatrix s t p u) B x i)| ≤
        haloRecoveryRhsError p u q 2 epsilon := by
  dsimp only
  let band := PhaseCellBand.width p u
  let B := cyclicPrincipalBoundary s t band a n
  let Y := boundarySolutionField B solution
  have hY := boundarySolutionField_magnitude q (stableInteriorExponent p 2) B solution hmag
  have hYerror := boundarySolutionField_error q B solution x epsilon herror
  have hp : 0 < p := by have := axis.hp; omega
  have htheta : 0 < (t : ℝ)/s-1 := lt_of_lt_of_le (by positivity) axis.hθ
  have hcount := couplingCountExponent_spec p u
  have hmass := couplingOffsets_mass_le_two axis.hst axis.hα p u axis.hp axis.hpacket
    axis.hαu axis.hθ axis.hgap axis.hbudget
  have hpiece (b c : ℕ) (hc : c ≤ s)
      (hB : haloBoundary s t band b c ⊆ B) (i : ZMod s) :
      ‖value q (guardedCouplingRowField (2^15*p) q t u band b c true Y C i)‖ ≤
          (2 : ℝ)^recoveryRhsExponent p 2 (stableInteriorExponent p 2) (couplingCountExponent p u) ∧
      Fits w (guardedCouplingRowField (2^15*p) q t u band b c true Y C i) ∧
      |(value q (guardedCouplingRowField (2^15*p) q t u band b c true Y C i)).re-
        ((value q (C i)).re-SchurDominance.couple (realMatrix s t p u) (haloBoundary s t band b c) x i)| ≤
          haloRecoveryRhsError p u q 2 epsilon := by
    have hnorm := guardedCouplingRowField_norm (a := b) (b := c) true hp axis.hst axis.hαu htheta axis.hgap
      axis.hbudget Y C hcount hC (fun j _ => hY j) i
    refine ⟨hnorm,fits_of_value_power hw _ hnorm,?_⟩
    have hh := guardedCouplingRowField_error (A := 96) (a := b) (b := c) true (by decide) hp axis.hst
      axis.hαu htheta axis.hgap axis.hbudget hw Y C x (fun j => (value q (C j)).re)
      2 epsilon 0 hepsilon hcount hC (fun j _ => hY j)
      (fun j hj => hYerror j (hB hj)) hmass (by intro j; simp) hc i (Or.inl rfl)
    simpa only [haloRecoveryRhsError,Bool.true_eq_false,ite_true,add_zero] using hh
  have hleft : haloBoundary s t band a (a+min n (s-a)) ⊆ B := by
    dsimp only [B]
    rw [cyclicPrincipalBoundary_eq t band a n ha hn]
    exact Finset.subset_union_left
  have hright : haloBoundary s t band 0 (n-min n (s-a)) ⊆ B := by
    dsimp only [B]
    rw [cyclicPrincipalBoundary_eq t band a n ha hn]
    exact Finset.subset_union_right
  have hcouple := cyclicPrincipal_recovery_couple (t := t) p u a n ha hn x
  intro i hi
  by_cases hleftI : i ∈ haloInterior s t band a (a+min n (s-a))
  · dsimp only [band] at hleftI
    simp only [ite_eq_left hleftI]
    rw [hcouple.1 i hleftI]
    exact hpiece a _ (by omega) hleft i
  · have hrightI : i ∈ haloInterior s t band 0 (n-min n (s-a)) :=
      (Finset.mem_union.mp hi).resolve_left hleftI
    dsimp only [band] at hleftI
    simp only [ite_eq_right hleftI]
    rw [hcouple.2 i hrightI]
    exact hpiece 0 _ (by omega) hright i

/-- Stability of the joint interior recovery, independent of its execution schedule. -/
theorem cyclicRecovery_interior_error {s t p u l q a n : ℕ} [NeZero s] {alpha gap : ℝ}
    (axis : RecoveryAxisBounds s t p u l alpha gap)
    (C R D : ZMod s → GaussianInt) (x xI : ZMod s → ℝ) (delta eta : ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (cyclicPrincipalVertices s a n) x
      (fun i => (value q (C i)).re))
    (hxI : SchurDominance.Solves (realMatrix s t p u)
      (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n) xI (fun i => (value q (R i)).re))
    (hR : ∀ i ∈ cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n,
      |(value q (R i)).re-((value q (C i)).re-SchurDominance.couple (realMatrix s t p u)
        (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n) x i)| ≤ delta)
    (hD : PhaseCellInterface.ErrorOn (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n)
      (fun i => (value q (D i)).re) xI eta) :
    PhaseCellInterface.ErrorOn (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n)
      (fun i => (value q (D i)).re) x (eta+8*p*delta) := by
  let I := cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n
  let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by have := axis.hp; omega)
  have hmu : (0 : ℝ) < 1/(8*(p : ℝ)) := by positivity
  have hIB : Disjoint I B := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hj).2 hi
  have hpartition : I ∪ B = cyclicPrincipalVertices s a n :=
    Finset.union_sdiff_of_subset (cyclicPrincipalInterior_subset t (PhaseCellBand.width p u) a n)
  have hfull : SchurDominance.Solves (realMatrix s t p u) (I ∪ B) x
      (fun i => (value q (C i)).re) := by rw [hpartition]; exact hx
  have hs := SchurDominance.recovery_solves_error _ I B hIB _ hmu
    (SchurDominance.dominates_mono _ Finset.univ _ _ (Finset.subset_univ _) axis.hdom)
    x (fun i => (value q (C i)).re) xI (fun i => (value q (R i)).re) hfull hxI delta hR
  intro i hi
  have hh := hs i hi
  rw [div_div_eq_mul_div,div_one] at hh
  have hd := hD i hi
  rw [Real.norm_eq_abs] at hd ⊢
  have ht := abs_add_le ((value q (D i)).re-xI i) (xI i-x i)
  rw [sub_add_sub_cancel] at ht
  nlinarith only [hh,hd,ht]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
