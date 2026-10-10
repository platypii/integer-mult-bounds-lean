import IntegerMultBounds.Machine.CompactComplexSourceReadyLeaf
import IntegerMultBounds.Machine.CompactSpectatorInheritedGrid
import IntegerMultBounds.Machine.CompactComplexDenominatorPolicy

/-! The literal source-ready leaf result has its true normalized return grid.
The actual dependency Path derives signed guards; the physical output widths
remain the retained codec widths. The leaf return gap is exactly zero. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyLeafSemantics
noncomputable section
open CompactGadgetReservationShape (Shape)
open Networks
open CompactComplexRecursiveGeometry
open CompactRecursiveDependencyBudget (Path)
open CompactSpectatorInheritedGrid (Grid decoded kernelList dependencyCoefficient)
open CompactSpectatorLeafGuardOriginal (Direction result)
variable {sh : Shape} {left k : ℕ}

theorem result_width (dir : Direction) (rows ell p : ℕ) (rho : Fin sh.chunk)
    (visit : Visit sh.active left k) (hp : 2*sh.bits≤p)
    (f : CompactSpectatorVisitGeometry.Array (NativePolynomialStageShape.shape sh ell p) rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p) :
    ∀ i,((result dir (NativePolynomialStageShape.shape sh ell p) rows ell (p-2*sh.bits) rho visit f) i).1.length=
        CompactNativeRoleHeaders.recordWidth sh p ∧
      ((result dir (NativePolynomialStageShape.shape sh ell p) rows ell (p-2*sh.bits) rho visit f) i).2.length=
        CompactNativeRoleHeaders.recordWidth sh p := by
  have hf := CompactSpectatorInheritedGrid.width_from_retained_role
    (NativePolynomialStageShape.shape sh ell p) rows ell p hp f hw
  have hout : CompactSpectatorInheritedGrid.Width (NativePolynomialStageShape.shape sh ell p) rows ell (p-2*sh.bits)
      (result dir (NativePolynomialStageShape.shape sh ell p) rows ell (p-2*sh.bits) rho visit f) := by
    cases dir
    · exact CompactSpectatorLeafLoop.width_run _ _ _ _ _ _ _ f hf
    · exact CompactSpectatorInverseLeafLoop.width_run _ _ _ _ _ _ _ f hf
  intro i
  have hi := hout i
  have hwidth : CompactNativeRoleHeaders.recordWidth sh p=
      ButterflyGuard.width (ButterflyIndependentGuardHeaders.reservation sh.bits (p-2*sh.bits)) sh.bits := by
    unfold CompactNativeRoleHeaders.recordWidth ButterflyGuard.width ButterflyGuard.halfWidth
      ButterflyIndependentGuardHeaders.reservation
    omega
  change _=ButterflyGuard.width (ButterflyIndependentGuardHeaders.reservation sh.bits (p-2*sh.bits)) sh.bits ∧
    _=ButterflyGuard.width (ButterflyIndependentGuardHeaders.reservation sh.bits (p-2*sh.bits)) sh.bits at hi
  rwa [←hwidth] at hi

/-- The actual Path and retained precision derive the full directional Walsh
semantics at the leaf target; no contraction or supplied numerical guard is used. -/
theorem result_from_path (dir : Direction) (rows ell metadataP : ℕ) (rho : Fin sh.chunk)
    {levels frames returned : ℕ} (path : Path sh.active left k levels frames returned)
    (originalP C n : ℕ) (hP : 2*sh.bits≤metadataP)
    (hbaseline : originalP≤metadataP-2*sh.bits) (hchunk : dependencyCoefficient C≤sh.chunk)
    (f : CompactSpectatorVisitGeometry.Array (NativePolynomialStageShape.shape sh ell metadataP) rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh metadataP ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh metadataP)
    (hg : Grid (NativePolynomialStageShape.shape sh ell metadataP) rows ell (metadataP-2*sh.bits) n
      (CompactRecursiveGridBudget.bound originalP C levels (frames+2*returned)) f)
    (row : Fin rows) (poly : Fin (2^ell)) :
    let shape := NativePolynomialStageShape.shape sh ell metadataP
    let q := metadataP-2*sh.bits
    let out := result dir shape rows ell q rho path.visit f
    Grid shape rows ell q (CompactComplexDenominatorPolicy.leafTarget n k)
      (CompactRecursiveGridBudget.bound originalP C levels (frames+2*returned)*4^(arity^k)) out ∧
      (fun x => decoded shape rows ell q (CompactComplexDenominatorPolicy.leafTarget n k) out
        (RecursiveInterchangeRows.pack row (FlatCoordinateLayout.index x poly)))=
        BinaryWalsh.kernelRun (kernelList shape rho path.visit dir (arity^k) (by omega))
          (fun x => decoded shape rows ell q n f
            (RecursiveInterchangeRows.pack row (FlatCoordinateLayout.index x poly))) := by
  have hf := CompactSpectatorInheritedGrid.width_from_retained_role
    (NativePolynomialStageShape.shape sh ell metadataP) rows ell metadataP hP f hw
  have hguard := CompactSpectatorInheritedGrid.guard_from_path
    (NativePolynomialStageShape.shape sh ell metadataP) (metadataP-2*sh.bits) path originalP C (arity^k)
    hbaseline hchunk (CompactSpectatorLeafSemantics.count_le_bits _ rho path.visit)
  exact CompactSpectatorInheritedGrid.directional_semantics
    (NativePolynomialStageShape.shape sh ell metadataP) rows ell (metadataP-2*sh.bits) rho path.visit
    dir n _ f hf hg hguard row poly

theorem return_gap (n k : ℕ) :
    (n+arity^k)-CompactComplexDenominatorPolicy.leafTarget n k=0 := Nat.sub_self _

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyLeafSemantics
