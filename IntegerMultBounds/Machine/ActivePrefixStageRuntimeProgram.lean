import IntegerMultBounds.Machine.ActivePrefixStageRuntimeData

/-! One fixed tape bank and finite transition table for every positive stage
width. The original width and source/target slots are read physically. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageRuntimeProgram
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActiveRepairLayoutRecordsData (Array)
open ActivePrefixDirtyControlConjugationData (Kind)
open Networks.Shared50ModularControl (prime)
variable {s : Shape}

abbrev packedCount := ActivePrefixStageDispatchRun.count
abbrev singletonCount := ActivePrefixStageSingletonDispatch.count
abbrev commonCount := 68+packedCount+singletonCount
abbrev count := commonCount+3

theorem packed_le : 68+packedCount≤count := by unfold count commonCount; omega
theorem singleton_le : 68+singletonCount≤count := by unfold count commonCount; omega
theorem public_le : 68≤commonCount := by unfold commonCount; omega

def focus : Fin 2 → Fin commonCount := fun i => Fin.castLE public_le (ActivePrefixStageWidthOriginal.focus i)
theorem focus_injective : Function.Injective focus :=
  (Fin.castLE_injective public_le).comp ActivePrefixStageWidthOriginal.focus_injective

def packedFor (a b c e : Kind) (m n : ActivePrefixDirtyControlLoadProducer.Mode) :=
  SharedBankFamily.padProgram
    (ActivePrefixStageRuntimePlaced.program (ActivePrefixStageDispatchRun.programFor a b c e m n)
      ActivePrefixStageDispatchRun.permanent_le) packed_le

def singletonFor (m : ActivePrefixDirtyControlLoadProducer.Mode) :=
  SharedBankFamily.padProgram
    (ActivePrefixStageRuntimePlaced.program (ActivePrefixStageSingletonDispatch.programFor m)
      ActivePrefixStageSingletonDispatch.permanent_le) singleton_le

def programFor (a b c e : Kind) (m n r : ActivePrefixDirtyControlLoadProducer.Mode) :=
  ActivePrefixStageWidthBranch.program focus focus_injective (packedFor a b c e m n) (singletonFor r)
def program := programFor .tPure .tNegative .uPure .uNegative .pure .pure .pure

def common (d : Inputs s) (x : Array s d.rows) :=
  SharedBankStageInput.raw (ActivePrefixStageWidthOriginal.caller d x) commonCount
def bank (d : Inputs s) (x : Array s d.rows) := CleanSubbank.bank (s:=3) (common d x)

theorem bank_eq_raw (d : Inputs s) (x : Array s d.rows) :
    bank d x=SharedBankStageInput.raw (ActivePrefixStageWidthOriginal.caller d x) count :=
  SharedBankFamily.raw_append _ public_le 3

theorem sources (d : Inputs s) (x : Array s d.rows) :
    SharedBank.payload (common d x) focus=ActivePrefixStageWidthPlaced.sources
      (RecursiveChildQuotientsConstant.bits d.stage.f) := by
  have h := SharedBankRawCompose.payload_raw (ActivePrefixStageWidthOriginal.caller d x)
    (Fin.castLE public_le) (fun _ => rfl)
  have hh := congrArg (fun v => SharedBank.payload v ActivePrefixStageWidthOriginal.focus) h
  exact hh.trans (ActivePrefixStageWidthOriginal.sources d x)

theorem packed_runs (a b c e : Kind) (m n : ActivePrefixDirtyControlLoadProducer.Mode)
    (d : Inputs s) (x y : Array s d.rows) (B : ℕ)
    (h : HoareTime (ActivePrefixStageDispatchRun.programFor a b c e m n)
      (fun v => v=ActivePrefixStageDispatchRun.bank d x)
      (fun v => v=ActivePrefixStageDispatchRun.bank d y) B) :
    HoareTime (packedFor a b c e m n) (fun v => v=bank d x) (fun v => v=bank d y) B := by
  have hh := SharedBankFamily.pad_clean_realizes packed_le _ _ _
    (ActivePrefixStageRuntimePlaced.runs _ ActivePrefixStageDispatchRun.permanent_le _ _ h)
  rw [bank_eq_raw,bank_eq_raw]
  exact hh

theorem singleton_runs (m : ActivePrefixDirtyControlLoadProducer.Mode)
    (d : Inputs s) (x y : Array s d.rows) (B : ℕ)
    (h : HoareTime (ActivePrefixStageSingletonDispatch.programFor m)
      (fun v => v=ActivePrefixStageSingletonDispatch.bank d x)
      (fun v => v=ActivePrefixStageSingletonDispatch.bank d y) B) :
    HoareTime (singletonFor m) (fun v => v=bank d x) (fun v => v=bank d y) B := by
  have hh := SharedBankFamily.pad_clean_realizes singleton_le _ _ _
    (ActivePrefixStageRuntimePlaced.runs _ ActivePrefixStageSingletonDispatch.permanent_le _ _ h)
  rw [bank_eq_raw,bank_eq_raw]
  exact hh

end
end IntegerMultBounds.Machine.ActivePrefixStageRuntimeProgram
