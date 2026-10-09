import IntegerMultBounds.Machine.ActivePrefixStageHeadersEndpoint
import IntegerMultBounds.Machine.ActivePrefixStageHeadersBudget
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullEarlyPlaced
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullLatePlaced

/-! Original shape/node/slot descriptors and one raw array are the complete
caller input. Every full-stage consumer descriptor is physically synthesized. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageFullData
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters ActivePrefixStageGeometry
open ActivePrefixStageHeadersData (Order)
open ActiveRepairLayoutRecordsData (Array)
open Networks.Shared50ModularControl (prime)
variable {s : Shape}

structure Inputs (s : Shape) where
  stage : Stage s
  rows : ℕ
  hG : 1≤s.guard
  hGK : s.guard+1≤s.chunk
  hr : 0<rows
  hrecord : s.bits+1≤s.payload

def descriptors (order : Order) (d : Inputs s) :=
  ActivePrefixStageHeadersEndpoint.inputs order d.stage d.rows d.hG d.hGK d.hr d.hrecord

def rawBank (d : Inputs s) (x : Array s d.rows) : Tapes 1 prime :=
  ⟨fun _ => 0,fun _ => ActiveTargetRotation.word x⟩
def caller (d : Inputs s) (st : ActivePrefixStageHeadersRouting.State) (x : Array s d.rows) :=
  (ActivePrefixStageHeadersRouting.caller (a := prime) st).append (rawBank d x)
def original (d : Inputs s) (x : Array s d.rows) := caller d
  (ActivePrefixStageHeadersPlaced.lift (ActivePrefixStageHeadersData.initial d.stage d.rows)) x
def ready (order : Order) (d : Inputs s) (x : Array s d.rows) :=
  caller d (ActivePrefixStageHeadersPlaced.finished order d.stage d.rows) x

def focus : Fin 23 → Fin 66 := fun i => ⟨43+i.val,by omega⟩
theorem focus_injective : Function.Injective focus := by
  intro i j h; apply Fin.ext; have := congrArg Fin.val h; simp [focus] at this; omega

theorem ready_sources (order : Order) (d : Inputs s) (x : Array s d.rows) :
    SharedBank.payload (ready order d x) focus=
      ActivePrefixEarlySequenceOriginalPlaced.sources (descriptors order d).gs
        (descriptors order d).bw (descriptors order d).hs x := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem late_sources (d : Inputs s) (x : Array s d.rows) :
    SharedBank.payload (ready .late d x) focus=
      ActiveRepairLayoutRecordsFullLatePlaced.common (descriptors .late d) x := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem caller_set (d : Inputs s) (st : ActivePrefixStageHeadersRouting.State) (x y : Array s d.rows) :
    SharedPlacementAlphabet.setTape (caller d st x) 65 (ActiveTargetRotation.word y) 0=caller d st y := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def earlyResult (d : Inputs s) (horder : d.stage.source.val<d.stage.target.val) (x : Array s d.rows) :=
  ActiveRepairLayoutRecordsFullEarlyData.result (descriptors .early d)
    (early_fits d.stage horder) (early_high_positive d.stage horder) (positive_H d.stage d.hG) x

def lateResult (d : Inputs s) (horder : d.stage.target.val<d.stage.source.val) (x : Array s d.rows) :=
  ActiveRepairLayoutRecordsFullLateData.result (descriptors .late d)
    (late_fits d.stage horder) (positive_before d.stage) (positive_H d.stage d.hG) x

end
end IntegerMultBounds.Machine.ActivePrefixStageFullData
