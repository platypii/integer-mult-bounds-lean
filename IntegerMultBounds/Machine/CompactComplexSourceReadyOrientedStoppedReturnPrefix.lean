import IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedReturnPrefix
import IntegerMultBounds.Machine.CompactComplexSourceReadyOrientationInvariants

/-! Prefix-preserving stopped semantics for the actual pre/post-oriented leaf.
The installed array is the literal forward leaf on the oriented selected input,
followed by the same saved-call orientation. No coarse replacement grid is used. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedStoppedReturnPrefix
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid
open CompactComplexRecursiveGeometry (arity Visit)
open CompactComplexSourceReadyOrientationInvariants (oriented oriented_width)
open CompactComplexNormalizedSpectatorHandoff (aligned)
open Networks

private theorem bounded_star {n M : ℕ} {z : ℂ} (hz : GaussianPrecision.BoundedGrid n M z) :
    GaussianPrecision.BoundedGrid n M (star z) := by
  obtain ⟨a,b,he,ha,hb⟩ := hz
  refine ⟨a,-b,?_,ha,by simpa only [abs_neg] using hb⟩
  have hc := congrArg star he
  simpa using hc

/-- Exact native conjugation on a retained prefix grid, using its genuine guard. -/
theorem orientation_grid (call : ComplexRecursiveCallSchema.Call) (sh : Shape) (rows ell q n M : ℕ)
    (f : Array sh rows ell) (hw : Width sh rows ell q f) (hg : Grid sh rows ell q n M f)
    (hguard : M<2^(half sh q)) :
    Grid sh rows ell q n M (oriented call f) ∧
    decoded sh rows ell q n (oriented call f)=fun i =>
      if call.inverse then star (decoded sh rows ell q n f i) else decoded sh rows ell q n f i := by
  have he : decoded sh rows ell q n (NativePolynomialConjugationData.array f)=
      fun i => star (decoded sh rows ell q n f i) := by
    funext i
    have hb := ButterflyGuard.represented_bound _ _ n M (hg i)
    have hlt : (M:ℤ)<(2^(half sh q):ℕ) := by exact_mod_cast hguard
    apply NativePolynomialConjugationData.decoded
    · simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using (hw i).2
    · exact hb.2.trans_lt hlt
  unfold oriented
  split_ifs
  · refine ⟨?_,he⟩
    intro i
    rw [congrFun he i]
    exact bounded_star (hg i)
  · exact ⟨hg,rfl⟩

/-- Actual pre/post-oriented leaf retains the original scalar-prefix grid.
Only actual spectator shifts enlarge their representation; the selected
returned array is the literal installed oriented leaf result. -/
theorem completed_prefix {ι : Type*} [DecidableEq ι]
    (call : ComplexRecursiveCallSchema.Call) (sh : Shape) (rows ell precision n completed k : ℕ)
    (progress : CompactComplexChildAlignmentBudget.Progress sh precision n completed (n+arity^(k+1)))
    (rho : Fin sh.chunk) {childLeft : ℕ} (visit : Visit sh.active childLeft (k+1))
    (selected : ι) (before : ι → Array sh rows ell) (result : Array sh rows ell)
    (hresult : result=oriented call (CompactSpectatorLeafGuardOriginal.result .forward sh rows ell
      (precision-2*sh.bits) rho visit (oriented call (before selected))))
    (hw : ∀ role,Width sh rows ell (precision-2*sh.bits) (before role))
    (g p C axes : ℕ) (ha : 0<sh.active) (hp : p+2*sh.bits≤precision)
    (haxes : axes+arity^(k+1)≤sh.bits) (hC : CompactFramedScalarGrid.growthConstant≤C)
    (hroom : dependencyCoefficient C+Nat.clog 2 (C+1)+CompactComplexScalarIntegerRows.guardBits≤sh.chunk)
    (hg : ∀ role,Grid sh rows ell (precision-2*sh.bits) n
      (CompactFramedScalarGrid.bound g (CompactRecursiveGridBudget.bound p C progress.parentLevels
        (progress.parentFrames+2*progress.parentReturned+axes))) (before role)) :
    (∀ role,Grid sh rows ell (precision-2*sh.bits) (n+arity^(k+1))
      (CompactFramedScalarGrid.bound g (CompactRecursiveGridBudget.bound p C progress.parentLevels
        (progress.parentFrames+2*(progress.parentReturned+arity^(k+1))+axes)))
      (aligned sh rows ell (arity^(k+1)) selected before result role)) ∧
    (∀ role,role≠selected → decoded sh rows ell (precision-2*sh.bits) (n+arity^(k+1))
      (aligned sh rows ell (arity^(k+1)) selected before result role)=
      decoded sh rows ell (precision-2*sh.bits) n (before role)) ∧
    n+arity^(k+1)≤CompactComplexDenominatorCapacity.ledger progress.R progress.baseline
      progress.parentLevels progress.parentFrames (progress.parentReturned+arity^(k+1)) progress.parentUsed := by
  let q := precision-2*sh.bits
  let gap := arity^(k+1)
  let M := CompactFramedScalarGrid.bound g (CompactRecursiveGridBudget.bound p C progress.parentLevels
    (progress.parentFrames+2*progress.parentReturned+axes))
  let input := oriented call (before selected)
  let leaf := CompactSpectatorLeafGuardOriginal.result .forward sh rows ell q rho visit input
  have hguard := CompactComplexStoppedEventProgress.prefix_guard_from_path progress.parentPath
    g p C axes gap precision ha hp haxes hC hroom
  change 4*(M*4^gap)<2^(half sh q) at hguard
  have hM : M≤M*4^gap := Nat.le_mul_of_pos_right M (pow_pos (by decide) gap)
  have hi := orientation_grid call sh rows ell q n M (before selected) (hw selected) (hg selected) (by omega)
  have hiw := oriented_width call sh rows ell q (before selected) (hw selected)
  have hleaf : Grid sh rows ell q (n+gap) (M*4^gap) leaf :=
    forward_grid sh rows ell q rho visit gap n M le_rfl input hiw hi.1 hguard
  have hlw : Width sh rows ell q leaf := by
    exact CompactSpectatorLeafLoop.width_run sh rows ell (ButterflyIndependentGuardHeaders.reservation sh.bits q)
      rho visit gap input hiw
  have hout := orientation_grid call sh rows ell q (n+gap) (M*4^gap) leaf hlw hleaf (by omega)
  have hd : gap≤half sh q+1 := by
    have hb := CompactSpectatorLeafSemantics.count_le_bits sh rho visit
    unfold gap q half ButterflyGuard.halfWidth
    omega
  have hpow : 2^gap≤4^gap := Nat.pow_le_pow_left (by decide) gap
  have hm := Nat.mul_le_mul_left M hpow
  have hs := CompactComplexChildGridAlignment.shared_grid sh rows ell q n M gap selected before
    (aligned sh rows ell gap selected before result) hg
    (by simpa only [aligned,ite_true,hresult] using hout.1)
    (fun role hr i => by
      simp only [aligned,ite_eq_right hr]
      exact CompactComplexChildGridPromoted.promotes sh rows ell q n M gap (before role)
        (hw role) (hg role) hd (by omega) i)
  refine ⟨?_,hs.2,?_⟩
  · intro role i
    exact GaussianPrecision.bound_mono
      (CompactComplexStoppedEventProgress.prefix_return_bound g p C progress.parentLevels
        progress.parentFrames progress.parentReturned axes gap) (hs.1 role i)
  · have hb := progress.before_live
    unfold CompactComplexDenominatorCapacity.ledger at *
    omega

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedStoppedReturnPrefix
