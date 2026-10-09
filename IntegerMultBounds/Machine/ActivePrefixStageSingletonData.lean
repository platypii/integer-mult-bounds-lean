import IntegerMultBounds.Machine.ActivePrefixStageFullErase
import IntegerMultBounds.Machine.ActiveTargetHighestLayoutOriginalGlobal

/-! The f=1 branch has no low packed target. Its single selected bit is the
physical highest-bit action, starting from the same thirteen original words
and raw array as the nontrivial full stage. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageSingletonData
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters ActivePrefixStageGeometry
open ActivePrefixStageHeadersData (Order)
open ActiveRepairLayoutRecordsData (Array)
open Networks.Shared50ModularControl (prime)
variable {s : Shape}

structure Inputs (s : Shape) extends ActivePrefixStageFullData.Inputs s where
  singleton : stage.f=1

def params (d : Inputs s) := parameters d.stage d.hG d.hGK

theorem zero_low (d : Inputs s) : (params d).n=0 := by
  change d.stage.f-1=0
  rw [d.singleton]

def focus : Fin 15 → Fin 66 := fun i => ⟨51+i.val,by omega⟩
theorem focus_injective : Function.Injective focus := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [focus] at this
  omega

def original (d : Inputs s) (x : Array s d.rows) := ActivePrefixStageFullData.original d.toInputs x
def ready (order : Order) (d : Inputs s) (x : Array s d.rows) := ActivePrefixStageFullData.ready order d.toInputs x

theorem sources (order : Order) (d : Inputs s) (x : Array s d.rows) :
    SharedBank.payload (ready order d x) focus=ActiveTargetHighestLayoutOriginalPlaced.sources
      (ActivePrefixStageFullData.descriptors order d.toInputs).hs x := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem caller_set (order : Order) (d : Inputs s) (x y : Array s d.rows) :
    SharedPlacementAlphabet.setTape (ready order d x) (focus 14) (ActiveTargetRotation.word y) 0=ready order d y :=
  ActivePrefixStageFullData.caller_set d.toInputs _ x y

def earlyResult (d : Inputs s) (horder : d.stage.source.val<d.stage.target.val) (x : Array s d.rows) :=
  ActiveTargetHighestLayoutGlobal.earlyAction s (params d) (earlyOffset d.stage) d.rows
    (early_fits d.stage horder) (early_high_positive d.stage horder) (positive_H d.stage d.hG)
    d.hr (by have := d.hrecord; omega) x

def lateResult (d : Inputs s) (horder : d.stage.target.val<d.stage.source.val) (x : Array s d.rows) :=
  ActiveTargetHighestLayoutGlobal.lateAction s (params d) (lateOffset d.stage) d.rows
    (late_fits d.stage horder) (positive_before d.stage) (positive_H d.stage d.hG)
    d.hr (by have := d.hrecord; omega) x

end
end IntegerMultBounds.Machine.ActivePrefixStageSingletonData
