import IntegerMultBounds.Machine.ActivePrefixStageDispatchPlaced

/-! One fixed physical program compares original slot numbers, reads its
flag, executes the original-input early or late stage, and erases the flag. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageDispatchRun
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs earlyResult lateResult)
open ActivePrefixStageDispatchData
open ActivePrefixStageDispatchPlaced (stage)
open ActivePrefixStageFullCompose (three three_runs)
open ActivePrefixDirtyControlConjugationData (Kind)
open ActiveRepairLayoutRecordsData (Array)
open Networks.Shared50ModularControl (prime)
variable {s : Shape}

abbrev earlyCount := ActivePrefixStageFullEarlyRun.count
abbrev lateCount := ActivePrefixStageFullLateRun.count
abbrev count := 67+earlyCount+lateCount+3
theorem early_le : 67+earlyCount≤count := by unfold count; omega
theorem late_le : 67+lateCount≤count := by unfold count; omega
theorem compare_le : 67+3≤count := by unfold count; omega
theorem permanent_le : 67≤count := by unfold count; omega

def comparator := SharedBankFamily.padProgram ActivePrefixStageDispatchPlaced.comparator compare_le
def cleanup := SharedBankFamily.padProgram ActivePrefixStageDispatchPlaced.cleanup compare_le
def earlyFor (m : ActivePrefixDirtyControlLoadProducer.Mode) :=
  SharedBankFamily.padProgram (stage (ActivePrefixStageFullEarlyRun.programFor m)) early_le
def lateFor (a b c e : Kind) (m : ActivePrefixDirtyControlLoadProducer.Mode) :=
  SharedBankFamily.padProgram (stage (ActivePrefixStageFullLateRun.programFor a b c e m)) late_le

def flagSlot : Fin count := Fin.castLE permanent_le flag
def test (sy : Fin count → Fin (prime+4)) := decide (sy flagSlot=bitSymbol true)
def branchesFor (a b c e : Kind) (m n : ActivePrefixDirtyControlLoadProducer.Mode) :=
  branch test (earlyFor n) (lateFor a b c e m)
def surround {q : ℕ} (M : Program count q prime) := three comparator M cleanup
def programFor (a b c e : Kind) (m n : ActivePrefixDirtyControlLoadProducer.Mode) :=
  surround (branchesFor a b c e m n)
def program := programFor .tPure .tNegative .uPure .uNegative .pure .pure

def bank (d : Inputs s) (x : Array s d.rows) := SharedBankStageInput.raw (caller d x) count
def flaggedBank (d : Inputs s) (x : Array s d.rows) := SharedBankStageInput.raw (flagged d x) count

theorem early_pad_runs (m : ActivePrefixDirtyControlLoadProducer.Mode)
    (d : Inputs s) (x y : Array s d.rows) (B : ℕ)
    (h : HoareTime (ActivePrefixStageFullEarlyRun.programFor m)
      (fun v => v=ActivePrefixStageFullEarlyRun.bank d x)
      (fun v => v=ActivePrefixStageFullEarlyRun.bank d y) B) :
    HoareTime (earlyFor m) (fun v => v=flaggedBank d x) (fun v => v=flaggedBank d y) B :=
  SharedBankFamily.pad_clean_realizes
    (M:=stage (ActivePrefixStageFullEarlyRun.programFor m)) early_le _ _ _
    (ActivePrefixStageDispatchPlaced.stage_runs _ d x y h)

theorem late_pad_runs (a b c e : Kind) (m : ActivePrefixDirtyControlLoadProducer.Mode)
    (d : Inputs s) (x y : Array s d.rows) (B : ℕ)
    (h : HoareTime (ActivePrefixStageFullLateRun.programFor a b c e m)
      (fun v => v=ActivePrefixStageFullLateRun.bank d x)
      (fun v => v=ActivePrefixStageFullLateRun.bank d y) B) :
    HoareTime (lateFor a b c e m) (fun v => v=flaggedBank d x) (fun v => v=flaggedBank d y) B :=
  SharedBankFamily.pad_clean_realizes
    (M:=stage (ActivePrefixStageFullLateRun.programFor a b c e m)) late_le _ _ _
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

theorem early_dispatch (a b c e : Kind) (m n : ActivePrefixDirtyControlLoadProducer.Mode)
    (d : Inputs s) (x y : Array s d.rows) (B : ℕ) (horder : d.stage.source.val<d.stage.target.val)
    (h : HoareTime (ActivePrefixStageFullEarlyRun.programFor n)
      (fun v => v=ActivePrefixStageFullEarlyRun.bank d x)
      (fun v => v=ActivePrefixStageFullEarlyRun.bank d y) B) :
    HoareTime (programFor a b c e m n) (fun v => v=bank d x) (fun v => v=bank d y)
      (ActivePrefixStageOrderCompare.cost d.stage+B+4) := by
  have hb := ActivePrefixStageDispatchCommon.branch_true test (earlyFor n) (lateFor a b c e m)
    (flaggedBank d x) (flaggedBank d y) (test_early d x horder) (early_pad_runs n d x y B h)
  exact (surround_runs (branchesFor a b c e m n) d x y hb).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

theorem late_dispatch (a b c e : Kind) (m n : ActivePrefixDirtyControlLoadProducer.Mode)
    (d : Inputs s) (x y : Array s d.rows) (B : ℕ) (horder : d.stage.target.val<d.stage.source.val)
    (h : HoareTime (ActivePrefixStageFullLateRun.programFor a b c e m)
      (fun v => v=ActivePrefixStageFullLateRun.bank d x)
      (fun v => v=ActivePrefixStageFullLateRun.bank d y) B) :
    HoareTime (programFor a b c e m n) (fun v => v=bank d x) (fun v => v=bank d y)
      (ActivePrefixStageOrderCompare.cost d.stage+B+4) := by
  have hb := ActivePrefixStageDispatchCommon.branch_false test (earlyFor n) (lateFor a b c e m)
    (flaggedBank d x) (flaggedBank d y) (test_late d x horder) (late_pad_runs a b c e m d x y B h)
  exact (surround_runs (branchesFor a b c e m n) d x y hb).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

def cost (D : ℕ) (d : Inputs s) (hn : 0<d.stage.f-1) (hb : 2≤s.guard) :=
  if h : d.stage.source.val<d.stage.target.val then
    ActivePrefixStageOrderCompare.cost d.stage+ActivePrefixStageFullEarlyRun.cost D d h+4
  else ActivePrefixStageOrderCompare.cost d.stage+
    ActivePrefixStageFullLateRun.cost D d (ActivePrefixStageOrderCompare.late_of_not_early d.stage h) hn hb+4

theorem runs (d : Inputs s) (x : Array s d.rows) (hn : 0<d.stage.f-1) (hb : 2≤s.guard)
    (hq3 : s.guard+3≤s.chunk)
    (hRE : (ActiveRepairLayoutRecordsHeadersData.repair (ActivePrefixStageFullData.descriptors .early d)).geom.addressBits+1≤s.payload)
    (hRL : (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair (ActivePrefixStageFullData.descriptors .late d)).geom.addressBits+1≤s.payload)
    (D : ℕ)
    (hDE : VaryingControlRepairDensity.earlyDensity s.chunk s.guard (d.stage.f-1)*
      ((ActiveRepairLayoutRecordsHeadersData.repair (ActivePrefixStageFullData.descriptors .early d)).geom.addressBits+1)≤D)
    (hDL : VaryingControlRepairDensity.lateDensity s.chunk s.guard (d.stage.f-1)*
      ((ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair (ActivePrefixStageFullData.descriptors .late d)).geom.addressBits+1)≤D) :
    HoareTime program (fun v => v=bank d x) (fun v => v=bank d (result d x)) (cost D d hn hb) := by
  by_cases h : d.stage.source.val<d.stage.target.val
  · have hr : result d x=earlyResult d h x := dite_eq_left h
    have hc : cost D d hn hb=ActivePrefixStageOrderCompare.cost d.stage+
        ActivePrefixStageFullEarlyRun.cost D d h+4 := dite_eq_left h
    have hh := early_dispatch .tPure .tNegative .uPure .uNegative .pure .pure d x _ _ h
      (ActivePrefixStageFullEarlyRun.runs d x h hq3 hRE D hDE)
    exact hh.consequence (fun _ hv => hv)
      (fun _ hv => hv.trans (congrArg (bank d) hr.symm)) hc.symm.le
  · have ho := ActivePrefixStageOrderCompare.late_of_not_early d.stage h
    have hr : result d x=lateResult d ho x := dite_eq_right h
    have hc : cost D d hn hb=ActivePrefixStageOrderCompare.cost d.stage+
        ActivePrefixStageFullLateRun.cost D d ho hn hb+4 := dite_eq_right h
    have hh := late_dispatch .tPure .tNegative .uPure .uNegative .pure .pure d x _ _ ho
      (ActivePrefixStageFullLateRun.runs d x ho hn hb hq3 hRL D hDL)
    exact hh.consequence (fun _ hv => hv)
      (fun _ hv => hv.trans (congrArg (bank d) hr.symm)) hc.symm.le

end
end IntegerMultBounds.Machine.ActivePrefixStageDispatchRun
