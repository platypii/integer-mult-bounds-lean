import IntegerMultBounds.Machine.CompactComplexSourceReadyNormalizedChildReturnPath

/-! The recovered parent payload is derived from its original caller words.
Installing a returned child updates exactly its selected role, independently
of all geometry, controller and ancestor-frame cells. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyInstalledPayload
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactSpectatorVisitGeometry (Array)
open SharedPlacementAlphabet (setTape)
open CompactComplexSourceReadyChildReturnPath (payloadPart)
variable {s c : ℕ}

theorem caller_payload (caller : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (pay : Tapes (1+c) 2)
    (hsource : caller.head CompactComplexNonleafRoleEntry.source=pay.head 0 ∧
      caller.tape CompactComplexNonleafRoleEntry.source=pay.tape 0)
    (hroles : ∀ j,caller.head (CompactComplexNonleafRoleEntry.roleTape j)=pay.head (Fin.natAdd 1 j) ∧
      caller.tape (CompactComplexNonleafRoleEntry.roleTape j)=pay.tape (Fin.natAdd 1 j)) :
    payloadPart (caller.append (SharedBank.empty 7 2))=pay := by
  have hs : (CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c).symm
      (Fin.castAdd 9 CompactComplexNativeRoleBridge.sourceSlot)=
      Fin.castAdd 7 CompactComplexNonleafRoleEntry.source := by
    apply Fin.ext
    rfl
  have hr (j : Fin c) : (CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c).symm
      (Fin.castAdd 9 (CompactComplexNativeRoleBridge.roleSlot j))=
      Fin.castAdd 7 (CompactComplexNonleafRoleEntry.roleTape j) := by
    apply Fin.ext
    rfl
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases (m:=1) (n:=c) with
  | left i =>
    fin_cases i
    all_goals simp only [CompactComplexSourceReadyChildReturnPath.permanent,
      SharedBank.payload,Tapes.reindex,Fin.addCases_left,hs,Tapes.append,Fin.addCases_left]
    first | exact hsource.1 | exact hsource.2
  | right j =>
    all_goals simp only [CompactComplexSourceReadyChildReturnPath.permanent,
      SharedBank.payload,Tapes.reindex,Fin.addCases_right,hr,Tapes.append,Fin.addCases_left]
    first | exact (hroles j).1 | exact (hroles j).2

/-- Result installation reconstructs the exact caller payload without an
independent post-return payload equality premise. -/
theorem install_payload (caller : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (pay : Tapes (1+c) 2) (selected : Fin c) (word : ℤ → Fin 6)
    (hsource : caller.head CompactComplexNonleafRoleEntry.source=pay.head 0 ∧
      caller.tape CompactComplexNonleafRoleEntry.source=pay.tape 0)
    (hroles : ∀ j,caller.head (CompactComplexNonleafRoleEntry.roleTape j)=pay.head (Fin.natAdd 1 j) ∧
      caller.tape (CompactComplexNonleafRoleEntry.roleTape j)=pay.tape (Fin.natAdd 1 j)) :
    payloadPart ((setTape caller (CompactComplexNonleafRoleEntry.roleTape selected) word 0).append
      (SharedBank.empty 7 2))=setTape pay (Fin.natAdd 1 selected) word 0 := by
  have hs : CompactComplexNonleafRoleEntry.source (s:=10+s) (c:=c)≠
      CompactComplexNonleafRoleEntry.roleTape selected := by
    intro h
    have hv := congrArg Fin.val h
    simp only [CompactComplexNonleafRoleEntry.source,CompactComplexNonleafRoleEntry.roleTape,
      CompactComplexSpectatorTargetBank.numericSlot,CompactComplexSpectatorTargetBank.roleSlot,
      CompactComplexNativeRoleBridge.roleSlot,CompactComplexControllerNativeFrame.nativeSlot,
      CompactComplexControllerNativeFrame.tapes,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  have hz : (0 : Fin (1+c))≠Fin.natAdd 1 selected := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero,Fin.val_natAdd] at hv
    omega
  apply caller_payload
  · simpa only [setTape,Function.update_of_ne hs,Function.update_of_ne hz] using hsource
  · intro j
    by_cases h : j=selected
    · subst j
      simp only [setTape,Function.update_self,and_self]
    · have hn : CompactComplexNonleafRoleEntry.roleTape (s:=10+s) j≠
          CompactComplexNonleafRoleEntry.roleTape selected := by
        intro he
        have hv := congrArg Fin.val he
        have hj : j.val≠selected.val := fun hv => h (Fin.ext hv)
        simp only [CompactComplexNonleafRoleEntry.roleTape,CompactComplexSpectatorTargetBank.roleSlot,
          CompactComplexNativeRoleBridge.roleSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
        omega
      have hp : Fin.natAdd 1 j≠Fin.natAdd 1 selected := fun he => h (Fin.natAdd_injective _ _ he)
      simpa only [setTape,Function.update_of_ne hn,Function.update_of_ne hp] using hroles j

/-- Original named caller words derive the exact returned array-family payload
required by normalized decoded return; no reconstructed payload is supplied. -/
theorem returned_payload (sh : Shape) (rows ell : ℕ)
    (caller : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (selected : Fin c) (before : Fin c → Array sh rows ell) (result : Array sh rows ell)
    (source : ℤ → Fin 6) (sourceHead : ℤ)
    (hsource : caller.head CompactComplexNonleafRoleEntry.source=sourceHead ∧
      caller.tape CompactComplexNonleafRoleEntry.source=source)
    (hroles : ∀ j,caller.head (CompactComplexNonleafRoleEntry.roleTape j)=0 ∧
      caller.tape (CompactComplexNonleafRoleEntry.roleTape j)=
        NativeZeroPadding.word (NativeZeroPaddingArray.word (before j))) :
    payloadPart ((setTape caller (CompactComplexNonleafRoleEntry.roleTape selected)
      (NativeZeroPadding.word (NativeZeroPaddingArray.word result)) 0).append (SharedBank.empty 7 2))=
      CompactComplexNormalizedSpectatorHandoff.returnedPayload sh rows ell selected source sourceHead before result := by
  have words_eq (f : Array sh rows ell) :
      NativeSignedGapPromoteReturn.word (CompactComplexStoppedGridHandoff.words f)=
        NativeZeroPadding.word (NativeZeroPaddingArray.word f) := by
    rw [CompactComplexStoppedGridHandoff.words_tape]
    rfl
  have h := install_payload caller
    (CompactComplexStoppedGridHandoff.payload sh rows ell source sourceHead before) selected
    (NativeZeroPadding.word (NativeZeroPaddingArray.word result))
    (by change caller.head CompactComplexNonleafRoleEntry.source=sourceHead ∧
          caller.tape CompactComplexNonleafRoleEntry.source=source
        exact hsource)
    (by intro j; simpa only [CompactComplexStoppedGridHandoff.payload,CyclicRowCopy.payload,Tapes.append,
      Fin.addCases_right,words_eq] using hroles j)
  refine h.trans ?_
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases (m:=1) (n:=c) with
  | left i =>
    fin_cases i
    all_goals simp [
      CompactComplexStoppedGridHandoff.payload,CyclicRowCopy.payload,Tapes.append]
  | right j =>
    by_cases hj : j=selected
    · subst j
      all_goals simp [
        CompactComplexStoppedGridHandoff.payload,CyclicRowCopy.payload,Tapes.append,words_eq]
    · have hp : Fin.natAdd 1 j≠Fin.natAdd 1 selected := fun he => hj (Fin.natAdd_injective _ _ he)
      all_goals simp [
        CompactComplexStoppedGridHandoff.payload,CyclicRowCopy.payload,Tapes.append,hj,
        hp,words_eq]

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyInstalledPayload
