import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsLate
import IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceOriginalBudget

/-! The original later payload machine placed on exactly twenty-three original
numeric/array ports. All private storage is initially and finally blank. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsPayloadLatePlaced
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActivePrefixDirtyControlConjugationData (FullArray Kind)
open ActivePrefixDirtyControlSequenceOriginalRun (count)
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
variable {s : Shape} {p : Parameters s} {offset rows t : ℕ}

def common (d : Inputs s p offset rows) (x : FullArray s rows) : Tapes 23 prime :=
  SharedBank.payload (ActivePrefixDirtyControlSequenceOriginalData.base d.gs d.bw d.hs x) (Fin.castAdd 30)
def ports (i : Fin 23) : Fin count := ⟨i.val,by have := i.isLt; have := ActivePrefixDirtyControlSequenceOriginalRun.header_le; omega⟩
theorem ports_injective : Function.Injective ports := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin count => k.val) h)

def programFor (a b c e : Kind) (focus : Fin 23 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (ActivePrefixDirtyControlSequenceOriginalRun.programFor a b c e)
    (CleanSubbank.placement ports focus hf)
def program (focus : Fin 23 → Fin t) (hf : Function.Injective focus) :=
  programFor .tPure .tNegative .uPure .uNegative focus hf

theorem base_private (d : Inputs s p offset rows) (x : FullArray s rows) (i : Fin 53) (hi : 23 ≤ i.val) :
    (ActivePrefixDirtyControlSequenceOriginalData.base d.gs d.bw d.hs x).head i=0 ∧
    (ActivePrefixDirtyControlSequenceOriginalData.base d.gs d.bw d.hs x).tape i=fun _ => blank := by
  have h7 : ¬ i.val<7 := by omega
  have h22 : ¬ i.val<22 := by omega
  have he7 : i.val≠7 := by omega
  have he22 : i.val≠22 := by omega
  simp [ActivePrefixDirtyControlSequenceOriginalData.base,ActivePrefixDirtyControlSequenceOriginalData.state,
    ActivePrefixDirtyControlSequenceOriginalData.head,ActivePrefixDirtyControlSequenceOriginalData.tape,
    h7,h22,he7,he22]

theorem native_payload (d : Inputs s p offset rows) (x : FullArray s rows) :
    SharedBank.payload (SharedBankStageInput.raw
      (ActivePrefixDirtyControlSequenceOriginalData.base d.gs d.bw d.hs x) count) ports=common d x := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals have hi : (ports i).val<53 := by have := i.isLt; change i.val<53; omega
  all_goals simp only [SharedBankStageInput.raw,hi,dite_true]
  all_goals rfl

theorem native_clean (d : Inputs s p offset rows) (x : FullArray s rows) :
    SharedBank.strip (SharedBankStageInput.raw
      (ActivePrefixDirtyControlSequenceOriginalData.base d.gs d.bw d.hs x) count) ports=
        SharedBank.empty count prime := by
  have h23 (i : Fin count) (hi : ¬∃j,ports j=i) : 23 ≤ i.val := by
    by_contra hn
    have hh : i.val<23 := by omega
    exact hi ⟨⟨i.val,hh⟩,Fin.ext rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> by_cases hi : ∃j,ports j=i
  all_goals simp only [hi,ite_true,ite_false]
  all_goals by_cases h53 : i.val<53
  all_goals simp only [SharedBankStageInput.raw,h53,dite_true,dite_false]
  all_goals first | exact (base_private d x ⟨i.val,h53⟩ (h23 i hi)).1 | exact (base_private d x ⟨i.val,h53⟩ (h23 i hi)).2

theorem common_set (d : Inputs s p offset rows) (x y : FullArray s rows) :
    setTape (common d x) 22 (ActiveTargetRotation.word y) 0=common d y := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem realizes {q budget : ℕ} (M : Program count q prime)
    (v : Tapes t prime) (focus : Fin 23 → Fin t) (hf : Function.Injective focus)
    (d : Inputs s p offset rows) (x y : FullArray s rows) (hsrc : SharedBank.payload v focus=common d x)
    (h : HoareTime M
      (fun w => w=SharedBankStageInput.raw (ActivePrefixDirtyControlSequenceOriginalData.base d.gs d.bw d.hs x) count)
      (fun w => w=SharedBankStageInput.raw (ActivePrefixDirtyControlSequenceOriginalData.base d.gs d.bw d.hs y) count) budget) :
    HoareTime (Placement.placed M (CleanSubbank.placement ports focus hf))
      (fun w => w=CleanSubbank.bank (s:=count) v)
      (fun w => w=CleanSubbank.bank (s:=count) (setTape v (focus 22) (ActiveTargetRotation.word y) 0)) budget := by
  refine CleanSubbank.realizes _ ports focus ports_injective hf v _ _ _ _ ?_ ?_
    (native_clean d x) (native_clean d y) ?_ h
  · exact (native_payload d x).trans hsrc.symm
  · rw [native_payload]
    simp only [CompactGadgetReservationPlacement.payload_set _ _ hf,hsrc,common_set]
  · simp only [CompactGadgetReservationPlacement.strip_set]

theorem runs_for (a b c e : Kind) (hfit : offset+p.f*p.q≤p.after) (hn : 0<p.n) (hb : 2≤p.b)
    (v : Tapes t prime) (focus : Fin 23 → Fin t) (hf : Function.Injective focus)
    (d : Inputs s p offset rows) (x : FullArray s rows) (hsrc : SharedBank.payload v focus=common d x) :
    HoareTime (programFor a b c e focus hf)
      (fun w => w=CleanSubbank.bank (s:=count) v)
      (fun w => w=CleanSubbank.bank (s:=count) (setTape v (focus 22)
        (ActiveTargetRotation.word (ActivePrefixDirtyControlSequenceRun.laterFor a b c e
          (ActivePrefixDirtyControlSequenceOriginalInputs.geometry hfit hn hb d) x)) 0))
      (ActivePrefixDirtyControlSequenceOriginalRun.costFor a b c e hfit hn hb d) :=
  realizes _ v focus hf d x _ hsrc (ActivePrefixDirtyControlSequenceOriginalRun.runs_for a b c e hfit hn hb d x)

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsPayloadLatePlaced
