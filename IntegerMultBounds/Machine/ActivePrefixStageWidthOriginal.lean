import IntegerMultBounds.Machine.ActivePrefixStageWidthBranch
import IntegerMultBounds.Machine.ActivePrefixStageDispatchData

/-! The width selector reads original public slot seven. Its separate flag
follows the existing original13/raw/direction-flag caller, so the source-order
flag is framed and can be used by either selected branch. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageWidthOriginal
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActiveRepairLayoutRecordsData (Array)
open Networks.Shared50ModularControl (prime)
open RecursiveChildQuotientsConstant (bits)
variable {s : Shape}

def caller (d : Inputs s) (x : Array s d.rows) :=
  (ActivePrefixStageDispatchData.caller d x).append (SharedBank.empty 1 prime)
def focus : Fin 2 → Fin 68 := ![7,67]
theorem focus_injective : Function.Injective focus := by decide

def marked (d : Inputs s) (x : Array s d.rows) :=
  ActivePrefixStageWidthPlaced.marked (caller d x) focus (bits d.stage.f)

def bank (d : Inputs s) (x : Array s d.rows) := CleanSubbank.bank (s := 3) (caller d x)
def markedBank (d : Inputs s) (x : Array s d.rows) := CleanSubbank.bank (s := 3) (marked d x)
def program := ActivePrefixStageWidthPlaced.program (a := prime) focus focus_injective
def cleanup := ActivePrefixStageWidthPlaced.cleanup (a := prime) focus focus_injective

theorem sources (d : Inputs s) (x : Array s d.rows) :
    SharedBank.payload (caller d x) focus=ActivePrefixStageWidthPlaced.sources (bits d.stage.f) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm

theorem runs (d : Inputs s) (x : Array s d.rows) : HoareTime program
    (fun v => v=bank d x) (fun v => v=markedBank d x) (ActivePrefixStageWidthSelector.cost (bits d.stage.f)) :=
  ActivePrefixStageWidthPlaced.runs (caller d x) focus focus_injective _ (sources d x)

theorem cleans (d : Inputs s) (x : Array s d.rows) : HoareTime cleanup
    (fun v => v=markedBank d x) (fun v => v=bank d x) 1 :=
  ActivePrefixStageWidthPlaced.cleans (caller d x) focus focus_injective _ (sources d x)

theorem packed_test (d : Inputs s) (x : Array s d.rows) :
    ActivePrefixStageWidthPlaced.test focus (markedBank d x).reads=true ↔ 2≤d.stage.f := by
  unfold markedBank marked
  rw [ActivePrefixStageWidthPlaced.test_eq,RecursiveChildQuotientsConstant.bits_value]
  simp
  omega

theorem singleton_test (d : Inputs s) (x : Array s d.rows) :
    ActivePrefixStageWidthPlaced.test focus (markedBank d x).reads=false ↔ d.stage.f=1 := by
  unfold markedBank marked
  rw [ActivePrefixStageWidthPlaced.test_eq,RecursiveChildQuotientsConstant.bits_value]
  have hp := d.stage.positiveWidth
  simp
  omega

theorem overhead_bound (d : Inputs s) :
    ActivePrefixStageWidthSelector.cost (bits d.stage.f)+4≤43*(d.rows*s.recordWidth) :=
  ActivePrefixStageWidthSelector.stage_cost_bound d.stage d.rows d.hG d.hGK d.hr d.hrecord

end
end IntegerMultBounds.Machine.ActivePrefixStageWidthOriginal
