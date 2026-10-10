import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafTargetSplit
import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafContraction
import IntegerMultBounds.Machine.CompactComplexSourceReadyScalarChildReadiness

/-! Actual tag2 target generation updates only original storage8 in the
canonical source-ready caller. No descriptor, role, or saved frame moves. -/
namespace IntegerMultBounds.Machine.NativeEndpointCharacterEntryStorage
noncomputable section
open CompactComplexNativeCodecFrame (bank permanentTapes)
open CompactComplexNonleafSpectatorTargetRestore (entry entryEquiv)
open CompactComplexSourceReadyNonleafTarget (targeted)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ}

private theorem storage_slot (i : Fin (10+s)) :
    (entryEquiv s c).symm (Fin.castAdd 9 (CompactComplexSpectatorTargetBank.oldSlot i))=
      CompactComplexNonleafRoleChildBank.storage (s:=s) (c:=c) i := by
  apply Fin.ext
  simp only [entryEquiv,finCongr_symm,finCongr_apply,Fin.val_cast,
    CompactComplexNonleafRoleChildBank.storage,Fin.val_castAdd]

private theorem setTape_reindex {l u a : ℕ} (e : Fin l ≃ Fin u) (v : Tapes l a)
    (i : Fin l) (f : ℤ → Fin (a+4)) (p : ℤ) :
    (setTape v i f p).reindex e=setTape (v.reindex e) (e i) f p := by
  apply congrArg₂ Tapes.mk <;> funext j
  all_goals obtain ⟨j,rfl⟩ := e.surjective j
  all_goals simp [setTape,Tapes.reindex,Function.update_apply,e.injective.eq_iff]

private theorem bank_setTape (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (payload : Tapes (1+c) 2) (i : Fin (10+s))
    (f : ℤ → Fin 6) (p : ℤ) :
    setTape (bank control queue scalar stage tail storage payload)
      (CompactComplexSpectatorTargetBank.oldSlot i) f p=
      bank control queue scalar stage tail (setTape storage i f p) payload := by
  unfold bank CompactComplexNativeRoleBridge.bank CompactComplexControllerNativeFrame.bank
    CompactComplexSpectatorTargetBank.oldSlot CompactComplexControllerNativeFrame.storageSlot
  rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_right,
    SharedPlacementAlphabet.setTape_append_right,SharedPlacementAlphabet.setTape_append_right,
    SharedPlacementAlphabet.setTape_append_left]

def storage (before : Tapes (10+s) 2) (target : ℕ) :=
  setTape before ⟨8,by omega⟩ (RadixZeroFill.encodedBinary (bits target)) 1

theorem targeted_bank (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (old : Tapes (10+s) 2) (payload : Tapes (1+c) 2) (frame : Tapes 9 2) (n : ℕ) :
    targeted (entry (bank control queue scalar stage tail old payload) frame) n=
      entry (bank control queue scalar stage tail (storage old n) payload) frame := by
  have hs := storage_slot (s:=s) (c:=c) (⟨8,by omega⟩ : Fin (10+s))
  unfold storage targeted entry CompactComplexNonleafRoleChildBank.target
  rw [←hs,←setTape_reindex,SharedPlacementAlphabet.setTape_append_left,bank_setTape]

theorem caller_storage (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (old : Tapes (10+s) 2) (payload : Tapes (1+c) 2) (frame : Tapes 9 2) (i : Fin (10+s)) :
    let caller := entry (bank control queue scalar stage tail old payload) frame
    caller.head (CompactComplexNonleafRoleChildBank.storage i)=old.head i ∧
    caller.tape (CompactComplexNonleafRoleChildBank.storage i)=old.tape i := by
  dsimp only
  rw [←storage_slot]
  simpa only [entry,Tapes.reindex,Equiv.symm_symm,Equiv.apply_symm_apply,
    Tapes.append,Fin.addCases_left] using
    CompactComplexSpectatorTargetBank.old_bank control queue scalar stage tail old payload i

theorem header_bank (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (old : Tapes (10+s) 2) (payload : Tapes (1+c) 2) (aux : Tapes 2 2) :
    Placement.active CompactComplexNonleafRoleEntry.headerPlacement
      (CompactComplexNonleafRoleSourceReturn.base
        (entry (bank control queue scalar stage tail old payload) (aux.append (SharedBank.empty 7 2))))=
      ActiveRepairRankHeadersCommands.bank stage := by
  have he : CompactComplexNonleafRoleSourceReturn.base
      (entry (bank control queue scalar stage tail old payload) (aux.append (SharedBank.empty 7 2)))=
      (bank control queue scalar stage tail old payload).append aux := by
    apply congrArg₂ Tapes.mk <;> funext i
    all_goals induction i using Fin.addCases (m:=permanentTapes (10+s) c) (n:=2) with
    | left i =>
      have hi : entryEquiv s c (Fin.castAdd 7 (Fin.castAdd 2 i))=Fin.castAdd 9 i := Fin.ext rfl
      simp only [entry,Tapes.reindex,Equiv.symm_symm,hi,Tapes.append,Fin.addCases_left]
    | right i =>
      have hi : entryEquiv s c (Fin.castAdd 7 (Fin.natAdd (permanentTapes (10+s) c) i))=
          Fin.natAdd (permanentTapes (10+s) c) (Fin.castAdd 7 i) := Fin.ext rfl
      simp only [entry,Tapes.reindex,Equiv.symm_symm,hi,Tapes.append,Fin.addCases_left,Fin.addCases_right]
  rw [he]
  exact CompactComplexSourceReadyScalarChildReadiness.entry_headers _ _ _ _ _ _ _ _

end
end IntegerMultBounds.Machine.NativeEndpointCharacterEntryStorage
