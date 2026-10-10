import IntegerMultBounds.Machine.CompactComplexStoppedLeafTensorSemantics
import IntegerMultBounds.Machine.CompactComplexCorrectedChildGridSemantics
import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedStoppedReturnPath

/-! The actual stopped output has the corrected child tensor interface at
the stopped denominator n+S. Its physical source is already pre-oriented
by tag0; this equality remains explicit when connecting the tag1 endpoint. -/
namespace IntegerMultBounds.Machine.CompactComplexCorrectedStoppedChildGridSemantics
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid (Width Grid decoded half dependencyCoefficient)
open CompactComplexSourceReadyOrientationInvariants (oriented)
open CompactComplexNonleafChildAddress (roles inputIndex outputWire outputAddress)
open CompactComplexCorrectedChildGridSemantics (tensor)
open CompactComplexNormalizedSpectatorHandoff (aligned)
variable {sh : Shape} {left k : ℕ}

/-- Literal tag1 output, acting on its actual physical source. -/
def installed (call : ComplexRecursiveCallSchema.Call) (rows ell q : ℕ)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+1))
    (source : Array sh rows ell) : Array sh rows ell :=
  oriented call (CompactSpectatorLeafGuardOriginal.result .forward sh rows ell q rho visit source)

/-- The literal corrected stopped return endpoint retains the installed
output word and its zero head after the genuine saved-frame pop. -/
theorem restored_installed_source {s : ℕ} (pcStack : Fin s)
    (call : ComplexRecursiveCallSchema.Call) (rows ell q : ℕ)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+1)) (source : Array sh rows ell)
    (v : Tapes (CompactComplexSourceReadyStoppedLeaf.publicTapes s
      CompactComplexSourceReadyScalarWorkspace.roles) 2)
    (scalar : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (target : ℕ) (older : ℤ → Fin 6) (origin : ℤ) :
    let child := installed call rows ell q rho visit source
    let endpoint := SharedPlacementAlphabet.setTape
      ((CompactComplexSourceReadyStoppedLeaf.ready
        (CompactComplexSourceReadyStoppedLeafCount.returned v (CompactSpectatorLeafAxis.word child)
          target)).append scalar)
      (CompactComplexSourceReadyCorrectedActualTable.savedStackSlot pcStack) older origin
    let port := Fin.castAdd CompactComplexSourceReadyScalarWorkspace.scratch
      (CompactComplexSourceReadyOrientation.source (s:=s)
        (c:=CompactComplexSourceReadyScalarWorkspace.roles))
    endpoint.tape port=CompactSpectatorLeafAxis.word child ∧ endpoint.head port=0 := by
  have h := CompactComplexSourceReadyOrientedControlsStopped.returned_source v
    (installed call rows ell q rho visit source) target
  have hn : Fin.castAdd CompactComplexSourceReadyScalarWorkspace.scratch
      (CompactComplexSourceReadyOrientation.source (s:=s)
        (c:=CompactComplexSourceReadyScalarWorkspace.roles)) ≠
      CompactComplexSourceReadyCorrectedActualTable.savedStackSlot pcStack := by
    rw [CompactComplexSourceReadyCorrectedActualTable.savedStackSlot_eq]
    intro he
    exact CompactComplexSourceReadyOrientationInvariants.savedSlot_ne_source pcStack
      (Fin.castAdd_injective _ _ he).symm
  dsimp only
  simpa only [SharedPlacementAlphabet.setTape,Function.update_of_ne hn,
    Tapes.append,Fin.addCases_left,CompactSpectatorLeafAxis.word,
    NativeZeroPadding.word,NativeZeroPaddingArray.word,ButterflyStreamData.full] using h

/-- The reached pre-orientation equality connects the physical tag1 output
to the corrected selected child tensor, for every role and address. -/
theorem installed_tensor (call : ComplexRecursiveCallSchema.Call) (rows ell q n M : ℕ)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+1))
    (original source : Array sh rows ell) (hpre : source=oriented call original)
    (hw : Width sh rows ell q original) (hg : Grid sh rows ell q n M original)
    (hguard : 4*(M*4^(arity^(k+1)))<2^(half sh q)) (hd : roles∣rows) :
    Grid sh rows ell q (n+arity^(k+1)) (M*4^(arity^(k+1)))
      (installed call rows ell q rho visit source) ∧
    ∀ i,decoded sh rows ell q (n+arity^(k+1)) (installed call rows ell q rho visit source) i=
      tensor call (fun wire address => decoded sh rows ell q n original
        (inputIndex sh rows ell hd rho visit i wire address))
        (outputWire sh rows ell hd i) (outputAddress sh rows ell hd rho visit i) := by
  subst source
  have h := CompactComplexStoppedLeafTensorSemantics.stopped_leaf_tensor_guarded
    call rows ell q n M rho visit original hw hg hguard
  refine ⟨?_,?_⟩
  · intro i
    let v := (CompactComplexNonleafChildAddress.layout sh rows ell hd).symm i
    exact (h (CompactComplexNonleafChildAddress.rowLayout rows hd v.1) v.2.2 v.2.1).1 i
  intro i
  exact CompactComplexStoppedLeafTensorSemantics.stopped_leaf_tensor_at_guarded
    call rows ell q n M rho visit original hw hg hguard hd i

/-- Literal stopped spectator promotion shares n+S with the selected
tensor output; untouched roles retain their original decoded values. -/
theorem installed_shared_grid {ι : Type*} [DecidableEq ι]
    (call : ComplexRecursiveCallSchema.Call) (rows ell q n M : ℕ)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+1))
    (selected : ι) (before : ι → Array sh rows ell) (source : Array sh rows ell)
    (hpre : source=oriented call (before selected))
    (hw : ∀ role,Width sh rows ell q (before role))
    (hg : ∀ role,Grid sh rows ell q n M (before role))
    (hguard : 4*(M*4^(arity^(k+1)))<2^(half sh q)) (hd : roles∣rows)
    (hcapacity : arity^(k+1)≤half sh q+1) :
    (∀ role,Grid sh rows ell q (n+arity^(k+1)) (M*4^(arity^(k+1)))
      (aligned sh rows ell (arity^(k+1)) selected before
        (installed call rows ell q rho visit source) role)) ∧
    (∀ role,role≠selected → decoded sh rows ell q (n+arity^(k+1))
      (aligned sh rows ell (arity^(k+1)) selected before
        (installed call rows ell q rho visit source) role)=decoded sh rows ell q n (before role)) := by
  have hc := installed_tensor call rows ell q n M rho visit (before selected) source hpre
    (hw selected) (hg selected) hguard hd
  have hpow : 2^(arity^(k+1))≤4^(arity^(k+1)) := Nat.pow_le_pow_left (by decide) _
  have hm := Nat.mul_le_mul_left M hpow
  have hsmall : M*2^(arity^(k+1))<2^(half sh q) := by omega
  exact CompactComplexChildGridAlignment.shared_grid sh rows ell q n M (arity^(k+1))
    selected before (aligned sh rows ell (arity^(k+1)) selected before
      (installed call rows ell q rho visit source)) hg
    (by simpa only [aligned,ite_true] using hc.1)
    (fun role hr i => by
      simp only [aligned,ite_eq_right hr]
      exact CompactComplexChildGridPromoted.promotes sh rows ell q n M _ (before role)
        (hw role) (hg role) hcapacity hsmall i)

/-- The original parent prefix reserve simultaneously pays the literal stopped
tensor, spectator promotion, and returned denominator ledger. -/
theorem installed_prefix_tensor {ι : Type*} [DecidableEq ι]
    (call : ComplexRecursiveCallSchema.Call) (sh : Shape) (rows ell precision n completed k : ℕ)
    (progress : CompactComplexChildAlignmentBudget.Progress sh precision n completed (n+arity^(k+1)))
    (rho : Fin sh.chunk) {childLeft : ℕ} (visit : Visit sh.active childLeft (k+1))
    (selected : ι) (before : ι → Array sh rows ell) (source : Array sh rows ell)
    (hpre : source=oriented call (before selected))
    (hd : roles∣rows)
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
      (aligned sh rows ell (arity^(k+1)) selected before
        (installed call rows ell (precision-2*sh.bits) rho visit source) role)) ∧
    (∀ i,decoded sh rows ell (precision-2*sh.bits) (n+arity^(k+1))
      (installed call rows ell (precision-2*sh.bits) rho visit source) i=
      tensor call (fun wire address => decoded sh rows ell (precision-2*sh.bits) n (before selected)
        (inputIndex sh rows ell hd rho visit i wire address))
        (outputWire sh rows ell hd i) (outputAddress sh rows ell hd rho visit i)) ∧
    (∀ role,role≠selected → decoded sh rows ell (precision-2*sh.bits) (n+arity^(k+1))
      (aligned sh rows ell (arity^(k+1)) selected before
        (installed call rows ell (precision-2*sh.bits) rho visit source) role)=
      decoded sh rows ell (precision-2*sh.bits) n (before role)) ∧
    n+arity^(k+1)≤CompactComplexDenominatorCapacity.ledger progress.R progress.baseline
      progress.parentLevels progress.parentFrames (progress.parentReturned+arity^(k+1)) progress.parentUsed := by
  have hguard := CompactComplexStoppedEventProgress.prefix_guard_from_path progress.parentPath
    g p C axes (arity^(k+1)) precision ha hp haxes hC hroom
  have ht := installed_tensor call rows ell (precision-2*sh.bits) n _ rho visit
    (before selected) source hpre (hw selected) (hg selected) hguard hd
  have hpref := CompactComplexSourceReadyOrientedStoppedReturnPrefix.completed_prefix
    call sh rows ell precision n completed k progress rho visit selected before
    (installed call rows ell (precision-2*sh.bits) rho visit source)
    (by rw [installed,hpre]) hw g p C axes ha hp haxes hC hroom hg
  exact ⟨hpref.1,ht.2,hpref.2⟩

end
end IntegerMultBounds.Machine.CompactComplexCorrectedStoppedChildGridSemantics
