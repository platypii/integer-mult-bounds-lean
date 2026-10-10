import IntegerMultBounds.Machine.CompactComplexControllerExactReturnBudget
import IntegerMultBounds.Machine.CompactComplexNonleafSpectatorTargetRestore
import IntegerMultBounds.Machine.CompactComplexNonleafRoleMergeCurrentBudget

/-! Literal serialization and retained-frame bridges for actual current-node
contraction followed by same-row cyclic merging. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafFinalGeometry
noncomputable section
open CompactComplexNativeCodecFrame (permanentTapes)
open CompactGadgetReservationShape (Shape)
variable {s c : ℕ}

theorem words_tape {N : ℕ} (f : Fin N → ButterflyStreamData.Coefficient) :
    NativeSignedGapReturn.word (CompactComplexStoppedGridHandoff.words f)=
      NativeZeroPadding.word (NativeZeroPaddingArray.word f) := by
  change NativeSignedGapPromoteReturn.word (CompactComplexStoppedGridHandoff.words f)=_
  rw [CompactComplexStoppedGridHandoff.words_tape]
  rfl

theorem contracted_role (sh : Shape) (rows ell gap : ℕ) (hd : c ∣ rows)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell) (j : Fin c) :
    CompactComplexControllerExactReturn.contracted gap
      (CompactNativeRoleReservedBridge.role sh rows c ell hd f j)=
    CompactNativeRoleReservedBridge.role sh rows c ell hd
      (CompactComplexControllerExactReturn.contracted gap f) j := rfl

theorem contracted_width {N w : ℕ} (gap : ℕ)
    (f : Fin N → ButterflyStreamData.Coefficient)
    (hw : ∀ i,(f i).1.length=w ∧ (f i).2.length=w) :
    ∀ i,(CompactComplexControllerExactReturn.contracted gap f i).1.length=w ∧
      (CompactComplexControllerExactReturn.contracted gap f i).2.length=w := by
  intro i
  simpa only [CompactComplexControllerExactReturn.contracted,NativeSignedGapScan.result_length] using hw i

private theorem permanent_slot (i : Fin (permanentTapes (10+s) c)) :
    CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c
      (Fin.castAdd 7 (Fin.castAdd 2 i))=Fin.castAdd 9 i := by apply Fin.ext; rfl
private theorem frame_slot (i : Fin 2) :
    CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c
      (Fin.castAdd 7 (Fin.natAdd (permanentTapes (10+s) c) i))=
      Fin.natAdd (permanentTapes (10+s) c) (Fin.castAdd 7 i) := by apply Fin.ext; rfl
private theorem work_slot (i : Fin 7) :
    CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c
      (Fin.natAdd (permanentTapes (10+s) c+2) i)=
      Fin.natAdd (permanentTapes (10+s) c) (Fin.natAdd 2 i) := by
  apply Fin.ext
  change (permanentTapes (10+s) c+2)+i.val=permanentTapes (10+s) c+(2+i.val)
  omega

theorem entry_append (v : Tapes (permanentTapes (10+s) c) 2)
    (frame : Tapes 2 2) (work : Tapes 7 2) :
    CompactComplexNonleafSpectatorTargetRestore.entry v (frame.append work)=
      (v.append frame).append work := by
  unfold CompactComplexNonleafSpectatorTargetRestore.entry Tapes.reindex
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left i => simp only [Equiv.symm_symm,permanent_slot,Tapes.append,Fin.addCases_left]
    | right i => simp only [Equiv.symm_symm,frame_slot,Tapes.append,Fin.addCases_left,Fin.addCases_right]
  | right i => simp only [Equiv.symm_symm,work_slot,Tapes.append,Fin.addCases_right]

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafFinalGeometry
