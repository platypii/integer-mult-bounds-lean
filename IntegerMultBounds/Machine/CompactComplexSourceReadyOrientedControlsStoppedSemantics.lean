import IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedControlsStopped

/-! Safety and exact decoded semantics of stopped post-orientation follow
from the original recursive Path and input inherited grid, including every
executed forward butterfly and the true committed leafTarget precision. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedControlsStoppedSemantics
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactRecursiveDependencyBudget (Path)
open CompactSpectatorInheritedGrid (Grid decoded dependencyCoefficient)
open CompactSpectatorLeafGuardOriginal (result)
open CompactComplexSourceReadyOrientationInvariants (oriented)
variable {sh : Shape} {left e levels frames returned : ℕ}

private theorem bounded_star {n M : ℕ} {z : ℂ} (hz : GaussianPrecision.BoundedGrid n M z) :
    GaussianPrecision.BoundedGrid n M (star z) := by
  obtain ⟨a,b,he,ha,hb⟩ := hz
  refine ⟨a,-b,?_,ha,by simpa only [abs_neg] using hb⟩
  have hc := congrArg star he
  simpa using hc

theorem post_from_path (call : ComplexRecursiveCallSchema.Call) (rows ell metadataP : ℕ)
    (rho : Fin sh.chunk) (path : Path sh.active left e levels frames returned)
    (originalP C n : ℕ) (hP : 2*sh.bits≤metadataP) (hr : 0<rows)
    (hbaseline : originalP≤metadataP-2*sh.bits) (hchunk : dependencyCoefficient C≤sh.chunk)
    (f : CompactSpectatorVisitGeometry.Array (NativePolynomialStageShape.shape sh ell metadataP) rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh metadataP ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh metadataP)
    (hg : Grid (NativePolynomialStageShape.shape sh ell metadataP) rows ell (metadataP-2*sh.bits) n
      (CompactRecursiveGridBudget.bound originalP C levels (frames+2*returned)) f) :
    let shape := NativePolynomialStageShape.shape sh ell metadataP
    let q := metadataP-2*sh.bits
    let out := result .forward shape rows ell q rho path.visit f
    let M := CompactRecursiveGridBudget.bound originalP C levels (frames+2*returned)*4^(arity^e)
    Grid shape rows ell q (CompactComplexDenominatorPolicy.leafTarget n e) M (oriented call out) ∧
      (∀ i,((oriented call out) i).1.length=CompactNativeRoleHeaders.recordWidth sh metadataP ∧
        ((oriented call out) i).2.length=CompactNativeRoleHeaders.recordWidth sh metadataP) ∧
      decoded shape rows ell q (CompactComplexDenominatorPolicy.leafTarget n e) (oriented call out)=
        fun i => if call.inverse then star (decoded shape rows ell q
          (CompactComplexDenominatorPolicy.leafTarget n e) out i) else decoded shape rows ell q
          (CompactComplexDenominatorPolicy.leafTarget n e) out i := by
  dsimp only
  let shape := NativePolynomialStageShape.shape sh ell metadataP
  let q := metadataP-2*sh.bits
  let out := result .forward shape rows ell q rho path.visit f
  let M := CompactRecursiveGridBudget.bound originalP C levels (frames+2*returned)*4^(arity^e)
  have hgrid := (CompactComplexSourceReadyLeafSemantics.result_from_path .forward rows ell metadataP rho
    path originalP C n hP hbaseline hchunk f hw hg ⟨0,hr⟩ ⟨0,pow_pos (by decide) ell⟩).1
  have hwidth := CompactComplexSourceReadyLeafSemantics.result_width .forward rows ell metadataP rho path.visit hP f hw
  have hstored := CompactSpectatorInheritedGrid.width_from_retained_role shape rows ell metadataP hP out hwidth
  have hguard := CompactSpectatorInheritedGrid.guard_from_path shape q path originalP C (arity^e)
    hbaseline hchunk (CompactSpectatorLeafSemantics.count_le_bits _ rho path.visit)
  have he : decoded shape rows ell q (CompactComplexDenominatorPolicy.leafTarget n e)
      (NativePolynomialConjugationData.array out)=fun i => star (decoded shape rows ell q
        (CompactComplexDenominatorPolicy.leafTarget n e) out i) := by
    funext i
    have hb := ButterflyGuard.represented_bound _ _ (CompactComplexDenominatorPolicy.leafTarget n e) M (hgrid i)
    have hlt : M<2^(CompactSpectatorInheritedGrid.half shape q) := by dsimp only [M] at *; omega
    have hlt' : (M:ℤ)<(2^(CompactSpectatorInheritedGrid.half shape q):ℕ) := by exact_mod_cast hlt
    apply NativePolynomialConjugationData.decoded
    · simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq,
        CompactSpectatorInheritedGrid.half,q,shape,NativePolynomialStageShape.bits] using (hstored i).2
    · exact hb.2.trans_lt hlt'
  unfold oriented
  split_ifs
  · refine ⟨?_,?_,he⟩
    · intro i
      have hei := congrFun he i
      change GaussianPrecision.BoundedGrid _ _ _
      rw [hei]
      exact bounded_star (hgrid i)
    · intro i
      simpa only [NativePolynomialConjugationData.array,NativePolynomialConjugationData.coefficient,
        NativePolynomialConjugationData.negative_length] using hwidth i
  · exact ⟨hgrid,hwidth,rfl⟩

private theorem current_ne_target {s c : ℕ} :
    CompactComplexNonleafRoleChildBank.current (s:=s) (c:=c)≠CompactComplexNonleafRoleChildBank.target := by
  intro he
  have hv := congrArg Fin.val he
  simp only [CompactComplexNonleafRoleChildBank.current,CompactComplexNonleafRoleChildBank.target,
    CompactComplexNonleafRoleChildBank.storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem current_ne_source {s c : ℕ} :
    Fin.castAdd 10 (Fin.castAdd CompactComplexSourceReadyWorkspace.leafTapes
      (CompactComplexNonleafRoleChildBank.current (s:=s) (c:=c)))≠
      CompactComplexSourceReadyOrientation.source := by
  intro he
  have hv := congrArg Fin.val he
  simp only [CompactComplexNonleafRoleChildBank.current,CompactComplexNonleafRoleChildBank.storage,
    CompactComplexSpectatorTargetBank.oldSlot,CompactComplexControllerNativeFrame.storageSlot,
    CompactComplexSourceReadyOrientation.source,NativePolynomialConjugationWorkspace.source,
    CompactComplexNonleafRoleEntry.source,CompactComplexSpectatorTargetBank.numericSlot,
    CompactComplexControllerNativeFrame.nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

/-- Post-orientation retains the actual committed live descriptor, literal
saved frame and all scratch banks; its source is the exact oriented result. -/
theorem endpoint {s c : ℕ} {shape : Shape} {rows ell : ℕ}
    (pcStack : Fin s) (call : ComplexRecursiveCallSchema.Call)
    (v : Tapes (CompactComplexSourceReadyStoppedLeaf.publicTapes s c) 2)
    (f : CompactSpectatorVisitGeometry.Array shape rows ell) (target : ℕ) :
    let before := CompactComplexSourceReadyStoppedLeaf.ready
      (CompactComplexSourceReadyStoppedLeafCount.returned v (CompactSpectatorLeafAxis.word f) target)
    let after := CompactComplexSourceReadyOrientation.output call before f
    after.tape CompactComplexSourceReadyOrientation.source=
        NativeZeroPadding.word (NativeZeroPaddingArray.word (oriented call f)) ∧
      after.head CompactComplexSourceReadyOrientation.source=0 ∧
      after.head (Fin.castAdd 10 (Fin.castAdd CompactComplexSourceReadyWorkspace.leafTapes
        CompactComplexNonleafRoleChildBank.current))=1 ∧
      after.tape (Fin.castAdd 10 (Fin.castAdd CompactComplexSourceReadyWorkspace.leafTapes
        CompactComplexNonleafRoleChildBank.current))=RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits target) ∧
      Placement.active (FiniteReturnStackAt.placement (CompactComplexSourceReadyOrientationInvariants.savedSlot pcStack)) after=
        Placement.active (FiniteReturnStackAt.placement (CompactComplexSourceReadyOrientationInvariants.savedSlot pcStack))
          (CompactComplexSourceReadyStoppedLeaf.ready v) := by
  dsimp only
  let before := CompactComplexSourceReadyStoppedLeaf.ready
    (CompactComplexSourceReadyStoppedLeafCount.returned v (CompactSpectatorLeafAxis.word f) target)
  have hs := CompactComplexSourceReadyOrientedControlsStopped.returned_source v f target
  have ho := CompactComplexSourceReadyOrientationInvariants.output_source call before f hs.1 hs.2
  have hc := CompactComplexSourceReadyOrientationInvariants.output_frame call before f
    (Fin.castAdd 10 (Fin.castAdd CompactComplexSourceReadyWorkspace.leafTapes
      CompactComplexNonleafRoleChildBank.current)) current_ne_source
  have hcurrent : before.head (Fin.castAdd 10 (Fin.castAdd CompactComplexSourceReadyWorkspace.leafTapes
      CompactComplexNonleafRoleChildBank.current))=1 ∧
      before.tape (Fin.castAdd 10 (Fin.castAdd CompactComplexSourceReadyWorkspace.leafTapes
      CompactComplexNonleafRoleChildBank.current))=
        RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits target) := by
    simp only [before,CompactComplexSourceReadyStoppedLeaf.ready,CompactComplexSourceReadyLeafPhase.ready,
      Tapes.append,Fin.addCases_left,CompactComplexSourceReadyStoppedLeafCount.returned,
      SharedPlacementAlphabet.setTape,Function.update_of_ne current_ne_target,Function.update_self]
    exact ⟨True.intro,True.intro⟩
  exact ⟨ho.1,ho.2,hc.1.trans hcurrent.1,hc.2.trans hcurrent.2,
    (CompactComplexSourceReadyOrientationInvariants.retained_savedSlot pcStack call before f).trans
      (CompactComplexSourceReadyOrientedControlsStopped.returned_saved pcStack v (CompactSpectatorLeafAxis.word f) target)⟩

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedControlsStoppedSemantics
