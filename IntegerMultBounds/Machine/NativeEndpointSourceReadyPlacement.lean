import IntegerMultBounds.Machine.NativeEndpointCharacterLeafPlacement
import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafContraction

/-! Character and uniform endpoint families borrow the first67 leaf tapes on
the actual source-ready recursive bank. The frame9, work10 and arbitrary
scalar suffix remain literal frames under the fixed executable permutation. -/
namespace IntegerMultBounds.Machine.NativeEndpointSourceReadyPlacement
noncomputable section
variable {s c q B w : ℕ}
open CompactComplexNativeCodecFrame (permanentTapes)
open CompactComplexSourceReadyWorkspace (leafTapes publicTapes)

abbrev callerTapes (s c : ℕ) := permanentTapes (10+s) c+9
abbrev tailTapes (w : ℕ) := (leafTapes+10)+w
abbrev fullTapes (s c w : ℕ) := CompactComplexSourceReadyWorkspace.tapes s c+w

private theorem caller_count : callerTapes s c=publicTapes s c := by
  rfl

private theorem full_count : callerTapes s c+tailTapes w=fullTapes s c w := by
  have h := caller_count (s:=s) (c:=c)
  unfold tailTapes fullTapes CompactComplexSourceReadyWorkspace.tapes
  omega

def placement : Fin (callerTapes s c+tailTapes w) ≃ Fin (fullTapes s c w) := finCongr full_count

private theorem caller_slot (i : Fin (callerTapes s c)) :
    placement (Fin.castAdd (tailTapes w) i)=
      Fin.castAdd w (Fin.castAdd 10 (Fin.castAdd leafTapes
        ((CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c).symm i))) := by
  apply Fin.ext
  simp only [placement,finCongr_apply,Fin.val_castAdd,Fin.val_cast,
    CompactComplexNonleafSpectatorTargetRestore.entryEquiv,finCongr_symm]

private theorem leaf_slot (i : Fin leafTapes) :
    placement (Fin.natAdd (callerTapes s c) (Fin.castAdd w (Fin.castAdd 10 i)))=
      Fin.castAdd w (Fin.castAdd 10 (Fin.natAdd (publicTapes s c) i)) := by
  apply Fin.ext
  simp only [placement,finCongr_apply,Fin.val_castAdd,Fin.val_cast,Fin.val_natAdd]
private theorem work_slot (i : Fin 10) :
    placement (Fin.natAdd (callerTapes s c) (Fin.castAdd w (Fin.natAdd leafTapes i)))=
      Fin.castAdd w (Fin.natAdd (publicTapes s c+leafTapes) i) := by
  apply Fin.ext
  simp only [placement,finCongr_apply,Fin.val_castAdd,Fin.val_cast,Fin.val_natAdd]
  have h := caller_count (s:=s) (c:=c)
  omega
private theorem suffix_slot (i : Fin w) :
    placement (Fin.natAdd (callerTapes s c) (Fin.natAdd (leafTapes+10) i))=
      Fin.natAdd (CompactComplexSourceReadyWorkspace.tapes s c) i := by
  apply Fin.ext
  simp only [placement,finCongr_apply,Fin.val_cast,Fin.val_natAdd]
  have h := caller_count (s:=s) (c:=c)
  unfold CompactComplexSourceReadyWorkspace.tapes
  omega

theorem reindex_bank (caller : Tapes (callerTapes s c) 2) (leaf : Tapes leafTapes 2)
    (work : Tapes 10 2) (suffix : Tapes w 2) :
    (caller.append ((leaf.append work).append suffix)).reindex placement=
      (((caller.reindex (CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c).symm).append
        leaf).append work).append suffix := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals obtain ⟨i,rfl⟩ := (placement (s:=s) (c:=c) (w:=w)).surjective i
  all_goals simp only [Tapes.reindex,Equiv.symm_apply_apply]
  all_goals induction i using Fin.addCases with
  | left i => simp only [caller_slot,Tapes.append,Fin.addCases_left,Equiv.symm_symm,
      Equiv.apply_symm_apply]
  | right i =>
    induction i using Fin.addCases (m:=leafTapes+10) (n:=w) with
    | right i => simp only [suffix_slot,Tapes.append,Fin.addCases_right]
    | left i =>
      induction i using Fin.addCases (m:=leafTapes) (n:=10) with
      | left i => simp only [leaf_slot,Tapes.append,Fin.addCases_left,Fin.addCases_right]
      | right i => simp only [work_slot,Tapes.append,Fin.addCases_left,Fin.addCases_right]

def program (h67 : 67≤leafTapes) (M : Program (callerTapes s c+67) q 2) :=
  reindex (NativeEndpointCharacterLeafPlacement.program
    (by unfold tailTapes; omega : 67≤tailTapes w) M) placement

/-- A physical local endpoint contract is placed into the real source-ready
bank without new tapes, retaining all unborrowed words and heads. -/
theorem runs (h67 : 67≤leafTapes) {M : Program (callerTapes s c+67) q 2}
    (v next : Tapes (permanentTapes (10+s) c) 2) (frame : Tapes 9 2)
    (leaf : Tapes leafTapes 2) (suffix : Tapes w 2)
    (hb : ∀ i : Fin 67,leaf.head ⟨i.val,lt_of_lt_of_le i.isLt h67⟩=0 ∧
      leaf.tape ⟨i.val,lt_of_lt_of_le i.isLt h67⟩=(fun _ => blank))
    (h : HoareTime M
      (fun z => z=(v.append frame).append (FixedHeaderBankCopy.empty 67))
      (fun z => z=(next.append frame).append (FixedHeaderBankCopy.empty 67)) B) :
    HoareTime (program h67 M)
      (fun z => z=(CompactComplexSourceReadyNonleafContraction.ready v frame leaf).append suffix)
      (fun z => z=(CompactComplexSourceReadyNonleafContraction.ready next frame leaf).append suffix) B := by
  have ht : 67≤tailTapes w := by unfold tailTapes;omega
  have hblank : ∀ i : Fin 67,
      (((leaf.append (SharedBank.empty 10 2)).append suffix).head ⟨i.val,lt_of_lt_of_le i.isLt ht⟩=0 ∧
      ((leaf.append (SharedBank.empty 10 2)).append suffix).tape ⟨i.val,lt_of_lt_of_le i.isLt ht⟩=(fun _ => blank)) := by
    intro i
    have he : (⟨i.val,lt_of_lt_of_le i.isLt ht⟩ : Fin (tailTapes w))=
        Fin.castAdd w (Fin.castAdd 10 ⟨i.val,lt_of_lt_of_le i.isLt h67⟩) := Fin.ext rfl
    rw [he]
    simpa only [Tapes.append,Fin.addCases_left] using hb i
  have hh := NativeEndpointCharacterLeafPlacement.runs ht (v.append frame) (next.append frame)
    ((leaf.append (SharedBank.empty 10 2)).append suffix) B hblank h
  have hr := hoare_reindex_eq hh (placement (s:=s) (c:=c) (w:=w))
  simpa only [program,reindex_bank,CompactComplexSourceReadyNonleafContraction.ready,
    CompactComplexSourceReadyWorkspace.bank,CompactComplexNonleafSpectatorTargetRestore.entry] using hr

end
end IntegerMultBounds.Machine.NativeEndpointSourceReadyPlacement
