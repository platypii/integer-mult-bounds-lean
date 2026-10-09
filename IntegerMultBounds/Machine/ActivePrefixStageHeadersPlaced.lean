import IntegerMultBounds.Machine.ActivePrefixStageHeadersRouting

/-! Complete synthesis plus paid descriptor duplication. Consumer ports43..64
are distinct actual tapes; original13 survive and every synthesis tape clears. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageHeadersPlaced
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData ActivePrefixStageHeadersSchedule
open ActivePrefixStageHeadersRouting
variable {a : ℕ} {s : Shape}

def consumerSources : Fin 22 → Fin 28 := ![0,1,2,20,3,4,5,2,13,14,15,16,17,18,19,0,2,20,10,21,4,5]
def consumerSlots : Fin 22 → Fin 65 := fun i => ⟨43+i.val,by omega⟩
theorem consumerSlots_injective : Function.Injective consumerSlots := by
  intro i j h; apply Fin.ext; have := congrArg Fin.val h; simp [consumerSlots] at this; omega

def lift (st : ActiveRepairRankHeadersCommands.State) : State := fun i =>
  if h : i.val<28 then st ⟨i.val,h⟩ else none

def finished (order : Order) (v : Stage s) (rows : ℕ) : State := fun i =>
  if h : i.val<13 then some (originalValues v rows ⟨i.val,h⟩)
  else if h : 43 ≤ i.val then ActivePrefixStageHeadersData.finished order v rows
    (consumerSources ⟨i.val-43,by omega⟩) else none

def schedule : List Command := [
  .copy 0 43 (by decide),
  .copy 1 44 (by decide),
  .copy 2 45 (by decide),
  .copy 20 46 (by decide),
  .copy 3 47 (by decide),
  .copy 4 48 (by decide),
  .copy 5 49 (by decide),
  .copy 2 50 (by decide),
  .copy 13 51 (by decide),
  .copy 14 52 (by decide),
  .copy 15 53 (by decide),
  .copy 16 54 (by decide),
  .copy 17 55 (by decide),
  .copy 18 56 (by decide),
  .copy 19 57 (by decide),
  .copy 0 58 (by decide),
  .copy 2 59 (by decide),
  .copy 20 60 (by decide),
  .copy 10 61 (by decide),
  .copy 21 62 (by decide),
  .copy 4 63 (by decide),
  .copy 5 64 (by decide),
  .erase 13,
  .erase 14,
  .erase 15,
  .erase 16,
  .erase 17,
  .erase 18,
  .erase 19,
  .erase 20,
  .erase 21]

theorem execute_eq (order : Order) (v : Stage s) (rows : ℕ) :
    execute schedule (lift (ActivePrefixStageHeadersData.finished order v rows))=finished order v rows := by
  funext i; fin_cases i
  all_goals simp [schedule,execute,eval,put,lift,finished,ActivePrefixStageHeadersData.finished,
    originalValues,outputs,consumerSources,Function.update]

theorem schedule_valid (order : Order) (v : Stage s) (rows : ℕ) :
    validSchedule schedule (lift (ActivePrefixStageHeadersData.finished order v rows)) := by
  simp [schedule,validSchedule,valid,eval,put,lift,ActivePrefixStageHeadersData.finished,
    originalValues,outputs,Function.update]

theorem lift_caller (st : ActiveRepairRankHeadersCommands.State) :
    caller (a := a) (lift st)=SharedBankStageInput.raw (ActiveRepairRankHeadersCommands.caller st) 65 := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals by_cases hi : i.val<28
  all_goals dsimp only [caller,lift,SharedBankStageInput.raw,ActiveRepairRankHeadersCommands.caller]
  all_goals simp only [hi,↓reduceDIte]
  all_goals rfl

def synthesis (order : Order) := SharedBankFamily.padProgram
  (ActivePrefixStageHeadersRun.program (a := a) order) (by decide : 43≤65)
def program (order : Order) := seq (synthesis (a := a) order) (compile (a := a) schedule).2

def cost (order : Order) (v : Stage s) (rows : ℕ) :=
  ActivePrefixStageHeadersRun.cost order v rows+1+
    scheduleCost schedule (lift (ActivePrefixStageHeadersData.finished order v rows))

theorem runs (order : Order) (v : Stage s) (rows : ℕ) (hG : 1≤s.guard)
    (horder : Ordered order v) :
    HoareTime (program (a := a) order) (fun x => x=caller (lift (initial v rows)))
      (fun x => x=caller (finished order v rows)) (cost order v rows) := by
  have hs := SharedBankFamily.pad_clean_realizes (s := 15) (M := ActivePrefixStageHeadersRun.program (a := a) order) (by decide : 43≤65)
    (ActiveRepairRankHeadersCommands.caller (a := a) (initial v rows))
    (ActiveRepairRankHeadersCommands.caller (ActivePrefixStageHeadersData.finished order v rows))
    (ActivePrefixStageHeadersRun.cost order v rows)
    (ActivePrefixStageHeadersRun.runs (a := a) order v rows hG horder)
  rw [←lift_caller,←lift_caller] at hs
  have hr := schedule_runs (a := a) schedule (lift (ActivePrefixStageHeadersData.finished order v rows))
    (schedule_valid order v rows)
  rw [execute_eq] at hr
  exact hs.seq hr

end
end IntegerMultBounds.Machine.ActivePrefixStageHeadersPlaced
