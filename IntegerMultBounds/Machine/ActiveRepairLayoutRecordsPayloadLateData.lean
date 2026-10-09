import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsPayloadLatePlaced
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsCleanAlphabet
import IntegerMultBounds.Machine.ActiveRepairArrayRecycle

/-! Literal original caller and actual/ideal arrays for the later payload,
repair and recycle stage. No formatted stream or generated header is supplied. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsPayloadLateData
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape setTape_append_left setTape_setTape)
open ActiveRepairLayoutRecordsAssemblyOriginalLateAfter (repair)
open ActivePrefixDirtyControlConjugationData (FullArray)
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

def extra (d : Inputs s p offset rows) : Tapes 8 prime :=
  ⟨fun _ => 1,fun i => if h : i.val<7 then RadixZeroFill.encodedBinary (d.gs ⟨i.val,h⟩)
    else RadixZeroFill.encodedBinary d.bw⟩
def caller (d : Inputs s p offset rows) (x : FullArray s rows) :=
  (setTape (ActiveRepairLayoutRecordsOriginalLateAlphabet.input d []) 237 (ActiveTargetRotation.word x) 0).append (extra d)
def focus : Fin 23 → Fin 252 := ![244,245,246,247,248,249,250,251,0,1,2,3,4,5,6,7,8,9,10,11,12,13,237]
theorem focus_injective : Function.Injective focus := by decide

def actual (d : Inputs s p offset rows) (x : FullArray s rows) :=
  ActiveRepairLayoutRecordsMove.move s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits p.activeSize
    (ActiveRepairLayoutPermutation.lateActual s p.q p.b p.n p.before p.after rows p.rho offset
      (p.f*p.q) .after (ActiveRepairLayoutKeysLate.positive (repair d))) x
def ideal (d : Inputs s p offset rows) (x : FullArray s rows) :=
  ActiveRepairLayoutRecordsMove.move s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits p.activeSize
    (ActiveRepairLayoutPermutation.lateIdeal s p.q p.b p.n p.before p.after rows p.rho offset
      (p.f*p.q) .after (ActiveRepairLayoutKeysLate.positive (repair d))) x
abbrev chunks (d : Inputs s p offset rows) (x : FullArray s rows) := ActiveRepairLayoutRecordsCleanAlphabet.Late.chunks d x

def repairOutput (d : Inputs s p offset rows) (x : FullArray s rows) :=
  (ActiveRepairLayoutRecordsCleanAlphabet.Late.output d (chunks d x)).append (extra d)

theorem caller_sources (d : Inputs s p offset rows) (x : FullArray s rows) :
    SharedBank.payload (caller d x) focus=ActiveRepairLayoutRecordsPayloadLatePlaced.common d x := by
  unfold caller
  rw [ActiveRepairLayoutRecordsOriginalLateAlphabet.input_literal]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl


theorem caller_private (d : Inputs s p offset rows) (x : FullArray s rows) :
    SharedBank.strip (caller d x) focus=SharedBank.empty 252 prime := by
  unfold caller
  rw [ActiveRepairLayoutRecordsOriginalLateAlphabet.input_literal]
  apply congrArg₂ Tapes.mk <;> funext i <;> by_cases hi : ∃j,focus j=i
  all_goals simp only [hi,ite_true,ite_false]
  all_goals fin_cases i
  all_goals first | rfl | exact (hi (by decide)).elim

theorem append_payload {u : ℕ} (v : Tapes 252 prime) :
    SharedBank.payload (v.append (SharedBank.empty u prime)) (fun i => Fin.castAdd u (focus i))=
      SharedBank.payload v focus := by
  apply congrArg₂ Tapes.mk <;> funext i <;> simp [Tapes.append]

theorem append_clean {u : ℕ} (v : Tapes 252 prime)
    (hclean : SharedBank.strip v focus=SharedBank.empty 252 prime) :
    SharedBank.strip (v.append (SharedBank.empty u prime))
      (fun i => Fin.castAdd u (focus i))=SharedBank.empty (252+u) prime := by
  apply congrArg₂ Tapes.mk <;> funext k
  all_goals induction k using (Fin.addCases (m:=252) (n:=u)) with
  | left i =>
    have he : (∃j,Fin.castAdd u (focus j)=Fin.castAdd u i) ↔ ∃j,focus j=i := by
      constructor
      · rintro ⟨j,hj⟩; exact ⟨j,Fin.castAdd_injective _ _ hj⟩
      · rintro ⟨j,rfl⟩; exact ⟨j,rfl⟩
    first
    | simpa only [SharedBank.strip,Tapes.append,Fin.addCases_left,he,SharedBank.empty]
        using congrFun (congrArg Tapes.head hclean) i
    | simpa only [SharedBank.strip,Tapes.append,Fin.addCases_left,he,SharedBank.empty]
        using congrFun (congrArg Tapes.tape hclean) i
  | right i =>
    have hn : ¬∃j,Fin.castAdd u (focus j)=Fin.natAdd 252 i := by
      rintro ⟨j,hj⟩
      have hv := congrArg Fin.val hj
      simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
      have := (focus j).isLt
      omega
    simp only [hn,ite_false,Tapes.append,Fin.addCases_right,SharedBank.empty]

theorem bank_clean {u : ℕ} (d : Inputs s p offset rows) (x : FullArray s rows) :
    SharedBank.strip ((caller d x).append (SharedBank.empty u prime))
      (fun i => Fin.castAdd u (focus i))=SharedBank.empty (252+u) prime :=
  append_clean (caller d x) (caller_private d x)

theorem caller_set (d : Inputs s p offset rows) (x y : FullArray s rows) :
    setTape (caller d x) 237 (ActiveTargetRotation.word y) 0=caller d y := by
  unfold caller
  rw [show (237:Fin 252)=Fin.castAdd 8 (237:Fin 244) from rfl,setTape_append_left]
  simp only [setTape_setTape]

theorem input_set (d : Inputs s p offset rows) (cs : List (List Bool)) :
    setTape (ActiveRepairLayoutRecordsOriginalLateAlphabet.input d []) 237
      ((ActiveRepairLayoutRecordsOriginalLateAlphabet.input d cs).tape 237) 0=
        ActiveRepairLayoutRecordsOriginalLateAlphabet.input d cs := by
  simp only [ActiveRepairLayoutRecordsOriginalLateAlphabet.input_literal]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem repair_input (d : Inputs s p offset rows) (x : FullArray s rows) :
    caller d (actual d x)=(ActiveRepairLayoutRecordsCleanAlphabet.Late.input d (chunks d x)).append (extra d) := by
  have hr : ActiveTargetRotation.word (actual d x)=
      (ActiveRepairLayoutRecordsOriginalLateAlphabet.input d (chunks d x)).tape 237 := by
    rw [ActiveRepairLayoutRecordsOriginalLateAlphabet.input_array]
    exact ActiveRepairArrayRecycle.word_eq _
  unfold caller
  rw [hr,input_set]

theorem repair_output (d : Inputs s p offset rows) (x : FullArray s rows)
    (hfit : offset+p.f*p.q≤p.after) (hq3 : p.b+3≤p.q) :
    repairOutput d x=setTape (caller d (actual d x)) 232 (ActiveTargetRotation.word (ideal d x)) 0 := by
  unfold repairOutput
  rw [ActiveRepairLayoutRecordsCleanAlphabet.Late.output_literal]
  rw [ActiveRepairLayoutRecordsOriginalLateAlphabet.output_ideal d x hfit hq3]
  rw [←ActiveRepairArrayRecycle.word_eq]
  rw [←setTape_append_left,←repair_input]
  rfl

theorem caller_head_raw (d : Inputs s p offset rows) (x : FullArray s rows) :
    (caller d x).head 237=0 := rfl

theorem caller_tape_raw (d : Inputs s p offset rows) (x : FullArray s rows) :
    (caller d x).tape 237=ActiveTargetRotation.word x := rfl

theorem recycle_result (d : Inputs s p offset rows) (x y : FullArray s rows) :
    ActiveRepairArrayRecycle.result (setTape (caller d x) 232 (ActiveTargetRotation.word y) 0) 232 237 y=
      caller d y := by
  unfold caller
  rw [ActiveRepairLayoutRecordsOriginalLateAlphabet.input_literal]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem recycle_runs (d : Inputs s p offset rows) (x : FullArray s rows)
    (hfit : offset+p.f*p.q≤p.after) (hq3 : p.b+3≤p.q) :
    HoareTime (ActiveRepairArrayRecycle.program (232:Fin 252) 237 (by decide) (by decide) prime)
      (fun v => v=repairOutput d x) (fun v => v=caller d (ideal d x)) (5*(rows*s.recordWidth)+10) := by
  rw [repair_output d x hfit hq3]
  have hh := ActiveRepairArrayRecycle.runs
    (setTape (caller d (actual d x)) 232 (ActiveTargetRotation.word (ideal d x)) 0)
    (232:Fin 252) 237 (by decide) (by decide) (actual d x) (ideal d x)
    (by simp [setTape]) (by simp only [setTape,Function.update_of_ne (by decide : (237:Fin 252)≠232)]; exact caller_tape_raw d _)
    (by simp [setTape]) (by simp only [setTape,Function.update_of_ne (by decide : (237:Fin 252)≠232)]; exact caller_head_raw d _)
  rwa [recycle_result] at hh

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsPayloadLateData
