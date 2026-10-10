import IntegerMultBounds.Machine.CompactComplexSavedStackTailInvariant
import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedClassifierTablePath

/-! Genuine fixed-width saved-stack histories lift to the reached corrected
controller, survive its classifier orientation, and supply the older blank
tail for its actual decoded return. The child pcSaved update writes the real
call code; no abstract execution callback supplies the erased-cell premise. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyReachedSavedStackHistory
noncomputable section
open Networks
open CompactComplexSourceReadyScalarWorkspace (roles tapes scratch)
open CompactComplexSourceReadyStoppedLeaf (publicTapes ready)
open CompactComplexSourceReadyCorrectedSavedReturnPath (publicSaved path)
open CompactComplexSourceReadyCorrectedActualTable (savedStackSlot)
open CompactComplexSavedStackTailInvariant (History Invariant history_tail)
open SharedPlacementAlphabet (setTape)
variable {s : ℕ}
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites
  CompactComplexCompletedLiveLower.schedule CompactComplexRolePhaseSite.roleCount
  CompactComplexCallReturn.addressCount CompactComplexCallReturn.addressWidth

/-- History at the actual decoded saved-PC port of the full fixed controller. -/
def Reached (pcStack : Fin s) (origin : ℤ) (v : Tapes (tapes s roles) 2) : Prop :=
  History (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3))
    origin (v.tape (savedStackSlot pcStack)) (v.head (savedStackSlot pcStack))

/-- The original public stack lifts unchanged through every private suffix. -/
theorem ready_history (pcStack : Fin s) (origin : ℤ) (v : Tapes (publicTapes s roles) 2)
    (scalar : Tapes scratch 2)
    (h : History (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3))
      origin (v.tape (publicSaved pcStack)) (v.head (publicSaved pcStack))) :
    Reached pcStack origin ((ready v).append scalar) := by
  have hs := CompactComplexSourceReadyCorrectedSavedReturnPath.ready_saved pcStack v scalar
  unfold Reached
  rw [hs.1,hs.2]
  exact h

/-- The real child PC-save update adds its actual fixed-width call frame. -/
theorem pc_saved_history (pcStack : Fin s) (call : ComplexRecursiveCallSchema.Call)
    (origin : ℤ) (v : Tapes (publicTapes s roles) 2)
    (h : History (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3))
      origin (v.tape (publicSaved pcStack)) (v.head (publicSaved pcStack))) :
    History (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3))
      origin ((CompactComplexNonleafRoleChildBank.pcSaved v pcStack call.site call.slot).tape (publicSaved pcStack))
      ((CompactComplexNonleafRoleChildBank.pcSaved v pcStack call.site call.slot).head (publicSaved pcStack)) := by
  have hp := History.push h (CompactComplexCallReturn.code call)
  simpa only [CompactComplexNonleafRoleChildBank.pcSaved,FiniteReturnStackAt.pushed,setTape,
    publicSaved,Function.update_self,CompactComplexCallReturn.code,
    CompactComplexRecursiveGeometry.arity] using hp

/-- The actual classifier's public orientation endpoint retains its literal
saved stack. This equality also applies when the selected call is inverse. -/
theorem classified_history {N : ℕ} (pcStack : Fin s) (call : ComplexRecursiveCallSchema.Call)
    (origin : ℤ) (v : Tapes (publicTapes s roles) 2)
    (f : Fin N → ButterflyStreamData.Coefficient)
    (h : History (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3))
      origin (v.tape (publicSaved pcStack)) (v.head (publicSaved pcStack))) :
    History (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3))
      origin ((CompactComplexSourceReadyOrientedControlsFrame.output call v f).tape (publicSaved pcStack))
      ((CompactComplexSourceReadyOrientedControlsFrame.output call v f).head (publicSaved pcStack)) := by
  have hne : publicSaved (s:=s) pcStack≠CompactComplexSourceReadyOrientedControlsFrame.source := by
    intro he
    have hv := congrArg Fin.val he
    simp only [publicSaved,CompactComplexNonleafRoleChildBank.storage,
      CompactComplexSpectatorTargetBank.oldSlot,CompactComplexControllerNativeFrame.storageSlot,
      CompactComplexSourceReadyOrientedControlsFrame.source,CompactComplexNonleafRoleEntry.source,
      CompactComplexSpectatorTargetBank.numericSlot,CompactComplexControllerNativeFrame.nativeSlot,
      Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  have hf := CompactComplexSourceReadyOrientedControlsFrame.frame call v f (publicSaved pcStack) hne
  rw [hf.1,hf.2]
  exact h

/-- A reached nonempty call frame returns through the real corrected decoder;
its older history supplies every blank erased cell and is physically restored. -/
theorem decoded_return_history (headerStack pcStack liveStack : Fin s)
    (call : ComplexRecursiveCallSchema.Call) (v : Tapes (tapes s roles) 2)
    (older : ℤ → Fin 6) (origin top : ℤ)
    (hHistory : History (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3))
      origin older top)
    (hstack : FiniteReturnStack.bank (v.tape (savedStackSlot pcStack)) (v.head (savedStackSlot pcStack))=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart older top (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (top+CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3))) :
    path headerStack pcStack liveStack 0 v
      (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)+5)
      (CompactComplexScheduledPCDecode.savedPC call)
      (setTape v (savedStackSlot pcStack) older top) ∧
    Reached pcStack origin (setTape v (savedStackSlot pcStack) older top) ∧
    Invariant (savedStackSlot pcStack) (setTape v (savedStackSlot pcStack) older top) := by
  refine ⟨CompactComplexSourceReadyCorrectedSavedReturnPath.full_return_path
    headerStack pcStack liveStack call v older top hstack (history_tail hHistory),?_,?_⟩
  · simpa only [Reached,setTape,Function.update_self] using hHistory
  · simpa only [Invariant,setTape,Function.update_self] using history_tail hHistory

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyReachedSavedStackHistory
