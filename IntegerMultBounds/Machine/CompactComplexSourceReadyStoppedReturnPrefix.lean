import IntegerMultBounds.Machine.CompactComplexSourceReadyFullNormalizedChildPaths

/-! Genuine stopped arithmetic closes the normalized physical return's exact
scalar-prefix invariant. The selected installed result is retained literally;
only spectators are shifted by the child's single-volume denominator gap. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedReturnPrefix
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid
open CompactComplexRecursiveGeometry (arity Visit)
open CompactComplexNormalizedSpectatorHandoff (aligned)

/-- Installed-result equality connects the actual leaf endpoint to the same
array family produced by the header-driven decoded return. -/
theorem aligned_leaf {ι : Type*} [DecidableEq ι]
    (sh : Shape) (rows ell q : ℕ) (rho : Fin sh.chunk) {left k : ℕ}
    (visit : Visit sh.active left k)
    (dir : CompactSpectatorLeafGuardOriginal.Direction) (selected : ι)
    (before : ι → Array sh rows ell) (result : Array sh rows ell)
    (hresult : result=CompactSpectatorLeafGuardOriginal.result dir sh rows ell q rho visit (before selected)) :
    aligned sh rows ell (arity^k) selected before result=
      CompactComplexChildGridPromoted.aligned sh rows ell q rho visit dir selected before := by
  funext role
  by_cases h : role=selected
  · subst role
    simpa only [aligned,CompactComplexChildGridPromoted.aligned,ite_true] using hresult
  · simp only [aligned,CompactComplexChildGridPromoted.aligned,ite_eq_right h]

/-- Actual leaf execution equality and the parent Path derive the unchanged
scalar-prefix grid, spectator values and advanced true returned-volume ledger.
No numerical grid or physical alignment is assumed for the child result. -/
theorem completed_prefix {ι : Type*} [DecidableEq ι]
    (sh : Shape) (rows ell precision n completed k : ℕ)
    (progress : CompactComplexChildAlignmentBudget.Progress sh precision n completed (n+arity^(k+1)))
    (rho : Fin sh.chunk) {childLeft : ℕ} (visit : Visit sh.active childLeft (k+1))
    (dir : CompactSpectatorLeafGuardOriginal.Direction) (selected : ι)
    (before : ι → Array sh rows ell) (result : Array sh rows ell)
    (hresult : result=CompactSpectatorLeafGuardOriginal.result dir sh rows ell (precision-2*sh.bits)
      rho visit (before selected))
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
  have hguard := CompactComplexStoppedEventProgress.prefix_guard_from_path progress.parentPath
    g p C axes (arity^(k+1)) precision ha hp haxes hC hroom
  have hs := CompactComplexStoppedEventProgress.stopped_prefix_grid sh rows ell (precision-2*sh.bits)
    rho visit dir selected before g p C progress.parentLevels progress.parentFrames progress.parentReturned axes n
    hw hg hguard
  rw [←aligned_leaf sh rows ell (precision-2*sh.bits) rho visit dir selected before result hresult] at hs
  refine ⟨hs.1,hs.2,?_⟩
  have hb := progress.before_live
  unfold CompactComplexDenominatorCapacity.ledger at *
  omega

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedReturnPrefix
