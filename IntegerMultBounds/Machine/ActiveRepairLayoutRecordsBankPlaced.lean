import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsBankInput

/-! Genuine fixed-many descriptor copies into the literal original repair
caller, retaining the whole producer and all unselected consumer tapes. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsBankPlaced
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairLayoutRecordsHeadersData ActiveRepairLayoutRecordsHeadersSchedule
open ActiveRepairLayoutRecordsHeadersCount ActiveRepairLayoutRecordsBankHeaders
open ActiveRepairLayoutRecordsBankInput
open ActiveRepairRankHeadersCommands (bank)
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

def slot : Fin 58 → Fin 226 := Fin.addCases (m := 43) (n := 15) (motive := fun _ => Fin 226) (Fin.castAdd 183)
  (fun i => Fin.natAdd 43 (destinations i))
theorem slot_injective : Function.Injective slot := by decide
def placement : Fin (58+168) ≃ Fin 226 := InjectivePlacement.placement slot slot_injective rfl

def input (d : Inputs s p offset rows) (rs : List Partition.Record) :=
  (bank (a := 1) (ready d)).append (raw rs)
def output (d : Inputs s p offset rows) (rs : List Partition.Record) :=
  (bank (a := 1) (ready d)).append (ActiveRepairEarlyOriginalPipelineEndpoint.input (repair d) rs)
def program := Placement.placed (copyProgram (a := 1)) placement

theorem active_input (d : Inputs s p offset rows) (rs : List Partition.Record) :
    Placement.active placement (input d rs)=
      (bank (ready d)).append (FixedHeaderBankCopy.empty 15) := by
  rw [placement,InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk
  · funext i
    induction i using (Fin.addCases (m := 43) (n := 15)) with
    | left i => simp [slot,input,Tapes.append]
    | right i => fin_cases i <;> rfl
  · funext i
    induction i using (Fin.addCases (m := 43) (n := 15)) with
    | left i => simp [slot,input,Tapes.append]
    | right i => fin_cases i <;> rfl

theorem active_output (d : Inputs s p offset rows) (rs : List Partition.Record) :
    Placement.active placement (output d rs)=ActiveRepairLayoutRecordsBankHeaders.output d := by
  rw [placement,InjectivePlacement.active_bank]
  have hm := metadata d rs
  apply congrArg₂ Tapes.mk
  · funext i
    induction i using (Fin.addCases (m := 43) (n := 15)) with
    | left i => simp [slot,output,Tapes.append]
    | right i => simpa [slot,output,Tapes.append,SharedBank.payload] using congrFun (congrArg Tapes.head hm) i
  · funext i
    induction i using (Fin.addCases (m := 43) (n := 15)) with
    | left i => simp [slot,output,Tapes.append]
    | right i => simpa [slot,output,Tapes.append,SharedBank.payload] using congrFun (congrArg Tapes.tape hm) i

theorem frame (d : Inputs s p offset rows) (rs : List Partition.Record) :
    Placement.extra placement (input d rs)=Placement.extra placement (output d rs) := by
  have not_slot (j : Fin 168) : ∀ i, placement (Fin.natAdd 58 j) ≠ slot i := by
    intro i hi
    rw [← InjectivePlacement.active_slot slot slot_injective (show 58+168=226 from rfl) i] at hi
    have h := congrArg Fin.val (placement.injective hi)
    simp only [Fin.val_natAdd,Fin.val_castAdd] at h
    omega
  have hb := blank_work d rs
  apply congrArg₂ Tapes.mk <;> funext j
  all_goals
    have hn := not_slot j
    generalize hx : placement (Fin.natAdd 58 j) = x at hn ⊢
    induction x using (Fin.addCases (m := 43) (n := 183)) with
    | left i => exact (hn (Fin.castAdd 15 i) (by simp [slot])).elim
    | right i =>
      have hi : ¬∃ k, destinations k=i := by
        rintro ⟨k,rfl⟩
        exact hn (Fin.natAdd 43 k) (by simp [slot])
      first
      | have h := congrFun (congrArg Tapes.head hb) i
        simpa only [SharedBank.strip,hi,ite_false,input,output,Tapes.append,Fin.addCases_right] using h.symm
      | have h := congrFun (congrArg Tapes.tape hb) i
        simpa only [SharedBank.strip,hi,ite_false,input,output,Tapes.append,Fin.addCases_right] using h.symm

theorem runs (d : Inputs s p offset rows) (rs : List Partition.Record) :
    HoareTime program (fun v => v=input d rs) (fun v => v=output d rs)
      (FixedHeaderBankCopy.cost (FixedHeaderBankCopy.ops 15) (words d)) := by
  have h := Placement.hoare_at (copies d) placement (input d rs) (active_input d rs)
  apply h.consequence (fun _ hi => hi) _ le_rfl
  rintro z ⟨w,hw,rfl⟩
  subst w
  rw [← active_output d rs,Placement.replace,frame d rs,Placement.view]

def originalInput (d : Inputs s p offset rows) (rs : List Partition.Record) :=
  (ActiveRepairLayoutRecordsHeadersRun.originalInput (a := 1) d).append (raw rs)
def prepareProgram := seq (extend (ActiveRepairLayoutRecordsHeadersCount.program (a := 1)) 183) program
def runtime (d : Inputs s p offset rows) := ActiveRepairLayoutRecordsHeadersCount.runtime d+1+
  FixedHeaderBankCopy.cost (FixedHeaderBankCopy.ops 15) (words d)

theorem prepares (d : Inputs s p offset rows) (rs : List Partition.Record) :
    HoareTime prepareProgram (fun v => v=originalInput d rs) (fun v => v=output d rs) (runtime d) := by
  have h := hoare_extend_eq (ActiveRepairLayoutRecordsHeadersCount.prepares (a := 1) d) (raw rs)
  rw [ActiveRepairLayoutRecordsHeadersRun.input_eq] at h
  exact h.seq (runs d rs)

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsBankPlaced
