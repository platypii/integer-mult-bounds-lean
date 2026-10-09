import IntegerMultBounds.Machine.ActivePrefixStageDispatchPlaced
import IntegerMultBounds.Machine.ActivePrefixStageSingletonRun

/-! One fixed physical program compares original slot numbers, reads its
flag, executes the original-input early or late stage, and erases the flag. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageSingletonDispatch
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageDispatchData
open ActivePrefixStageDispatchPlaced (stage)
open ActivePrefixStageFullCompose (three three_runs)

open ActiveRepairLayoutRecordsData (Array)
open Networks.Shared50ModularControl (prime)
variable {s : Shape}

abbrev earlyCount := ActivePrefixStageSingletonRun.count
abbrev lateCount := ActivePrefixStageSingletonRun.count
abbrev count := 67+earlyCount+lateCount+3
theorem early_le : 67+earlyCount≤count := by unfold count; omega
theorem late_le : 67+lateCount≤count := by unfold count; omega
theorem compare_le : 67+3≤count := by unfold count; omega
theorem permanent_le : 67≤count := by unfold count; omega

def comparator := SharedBankFamily.padProgram ActivePrefixStageDispatchPlaced.comparator compare_le
def cleanup := SharedBankFamily.padProgram ActivePrefixStageDispatchPlaced.cleanup compare_le
def early :=
  SharedBankFamily.padProgram (stage (ActivePrefixStageSingletonRun.earlierProgram)) early_le
def lateFor (m : ActivePrefixDirtyControlLoadProducer.Mode) :=
  SharedBankFamily.padProgram (stage (ActivePrefixStageSingletonRun.laterProgramFor m)) late_le

def flagSlot : Fin count := Fin.castLE permanent_le flag
def test (sy : Fin count → Fin (prime+4)) := decide (sy flagSlot=bitSymbol true)
def branchesFor (m : ActivePrefixDirtyControlLoadProducer.Mode) :=
  branch test early (lateFor m)
def surround {q : ℕ} (M : Program count q prime) := three comparator M cleanup
def programFor (m : ActivePrefixDirtyControlLoadProducer.Mode) :=
  surround (branchesFor m)
def program := programFor .pure

def bank (d : Inputs s) (x : Array s d.rows) := SharedBankStageInput.raw (caller d x) count
def flaggedBank (d : Inputs s) (x : Array s d.rows) := SharedBankStageInput.raw (flagged d x) count

theorem early_pad_runs
    (d : Inputs s) (x y : Array s d.rows) (B : ℕ)
    (h : HoareTime (ActivePrefixStageSingletonRun.earlierProgram)
      (fun v => v=CleanSubbank.bank (s:=ActivePrefixStageSingletonRun.privateCount) (ActivePrefixStageFullData.original d x))
      (fun v => v=CleanSubbank.bank (s:=ActivePrefixStageSingletonRun.privateCount) (ActivePrefixStageFullData.original d y)) B) :
    HoareTime early (fun v => v=flaggedBank d x) (fun v => v=flaggedBank d y) B :=
  SharedBankFamily.pad_clean_realizes
    (M:=stage (ActivePrefixStageSingletonRun.earlierProgram)) early_le _ _ _
    (ActivePrefixStageDispatchPlaced.stage_runs _ d x y h)

theorem late_pad_runs (m : ActivePrefixDirtyControlLoadProducer.Mode)
    (d : Inputs s) (x y : Array s d.rows) (B : ℕ)
    (h : HoareTime (ActivePrefixStageSingletonRun.laterProgramFor m)
      (fun v => v=CleanSubbank.bank (s:=ActivePrefixStageSingletonRun.privateCount) (ActivePrefixStageFullData.original d x))
      (fun v => v=CleanSubbank.bank (s:=ActivePrefixStageSingletonRun.privateCount) (ActivePrefixStageFullData.original d y)) B) :
    HoareTime (lateFor m) (fun v => v=flaggedBank d x) (fun v => v=flaggedBank d y) B :=
  SharedBankFamily.pad_clean_realizes
    (M:=stage (ActivePrefixStageSingletonRun.laterProgramFor m)) late_le _ _ _
    (ActivePrefixStageDispatchPlaced.stage_runs _ d x y h)

theorem surround_runs {q B : ℕ} (M : Program count q prime) (d : Inputs s) (x y : Array s d.rows)
    (h : HoareTime M (fun v => v=flaggedBank d x) (fun v => v=flaggedBank d y) B) :
    HoareTime (surround M) (fun v => v=bank d x) (fun v => v=bank d y)
      (ActivePrefixStageOrderCompare.cost d.stage+B+1+2) := by
  have hc := SharedBankFamily.pad_clean_realizes compare_le _ _ _
    (ActivePrefixStageDispatchPlaced.compare_runs d x)
  have he := SharedBankFamily.pad_clean_realizes compare_le _ _ _
    (ActivePrefixStageDispatchPlaced.cleanup_runs d y)
  exact three_runs (M:=comparator) (N:=M) (K:=cleanup) hc h he

theorem test_early (d : Inputs s) (x : Array s d.rows) (horder : d.stage.source.val<d.stage.target.val) :
    test (flaggedBank d x).reads=true := by
  change decide ((ActivePrefixStageOrderCompare.output (a:=prime) d.stage).tape 2 0=bitSymbol true)=true
  rw [ActivePrefixStageOrderCompare.early_flag d.stage horder]
  simp

theorem test_late (d : Inputs s) (x : Array s d.rows) (horder : d.stage.target.val<d.stage.source.val) :
    test (flaggedBank d x).reads=false := by
  change decide ((ActivePrefixStageOrderCompare.output (a:=prime) d.stage).tape 2 0=bitSymbol true)=false
  rw [ActivePrefixStageOrderCompare.late_flag d.stage horder]
  decide

theorem early_dispatch (m : ActivePrefixDirtyControlLoadProducer.Mode)
    (d : Inputs s) (x y : Array s d.rows) (B : ℕ) (horder : d.stage.source.val<d.stage.target.val)
    (h : HoareTime (ActivePrefixStageSingletonRun.earlierProgram)
      (fun v => v=CleanSubbank.bank (s:=ActivePrefixStageSingletonRun.privateCount) (ActivePrefixStageFullData.original d x))
      (fun v => v=CleanSubbank.bank (s:=ActivePrefixStageSingletonRun.privateCount) (ActivePrefixStageFullData.original d y)) B) :
    HoareTime (programFor m) (fun v => v=bank d x) (fun v => v=bank d y)
      (ActivePrefixStageOrderCompare.cost d.stage+B+4) := by
  have hb := ActivePrefixStageDispatchCommon.branch_true test early (lateFor m)
    (flaggedBank d x) (flaggedBank d y) (test_early d x horder) (early_pad_runs d x y B h)
  exact (surround_runs (branchesFor m) d x y hb).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

theorem late_dispatch (m : ActivePrefixDirtyControlLoadProducer.Mode)
    (d : Inputs s) (x y : Array s d.rows) (B : ℕ) (horder : d.stage.target.val<d.stage.source.val)
    (h : HoareTime (ActivePrefixStageSingletonRun.laterProgramFor m)
      (fun v => v=CleanSubbank.bank (s:=ActivePrefixStageSingletonRun.privateCount) (ActivePrefixStageFullData.original d x))
      (fun v => v=CleanSubbank.bank (s:=ActivePrefixStageSingletonRun.privateCount) (ActivePrefixStageFullData.original d y)) B) :
    HoareTime (programFor m) (fun v => v=bank d x) (fun v => v=bank d y)
      (ActivePrefixStageOrderCompare.cost d.stage+B+4) := by
  have hb := ActivePrefixStageDispatchCommon.branch_false test early (lateFor m)
    (flaggedBank d x) (flaggedBank d y) (test_late d x horder) (late_pad_runs m d x y B h)
  exact (surround_runs (branchesFor m) d x y hb).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

def result (d : ActivePrefixStageSingletonData.Inputs s) (x : Array s d.rows) :=
  if h : d.stage.source.val<d.stage.target.val then ActivePrefixStageSingletonData.earlyResult d h x
  else ActivePrefixStageSingletonData.lateResult d (ActivePrefixStageOrderCompare.late_of_not_early d.stage h) x

def cost (d : ActivePrefixStageSingletonData.Inputs s) :=
  if h : d.stage.source.val<d.stage.target.val then
    ActivePrefixStageOrderCompare.cost d.stage+ActivePrefixStageSingletonRun.earlyCost d h+4
  else ActivePrefixStageOrderCompare.cost d.stage+
    ActivePrefixStageSingletonRun.lateCost d (ActivePrefixStageOrderCompare.late_of_not_early d.stage h)+4

theorem runs (d : ActivePrefixStageSingletonData.Inputs s) (x : Array s d.rows) :
    HoareTime program (fun v => v=bank d.toInputs x)
      (fun v => v=bank d.toInputs (result d x)) (cost d) := by
  by_cases h : d.stage.source.val<d.stage.target.val
  · have hh := early_dispatch .pure d.toInputs x _ _ h
      (ActivePrefixStageSingletonRun.earlier_runs d x h)
    simpa only [program,result,cost,dite_eq_left h] using hh
  · have ho := ActivePrefixStageOrderCompare.late_of_not_early d.stage h
    have hh := late_dispatch .pure d.toInputs x _ _ ho
      (ActivePrefixStageSingletonRun.later_runs d x ho)
    simpa only [program,result,cost,dite_eq_right h] using hh

end
end IntegerMultBounds.Machine.ActivePrefixStageSingletonDispatch
