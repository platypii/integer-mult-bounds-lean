import IntegerMultBounds.Machine.ActivePrefixStageSingletonData
import IntegerMultBounds.Machine.ActivePrefixStageFullCompose

/-! Both ordered singleton stages are actual fixed finite programs: generate
all consumer words from the original thirteen, execute the single highest
selected-bit operation, then erase every generated consumer word. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageSingletonRun
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters ActivePrefixStageGeometry
open ActivePrefixStageSingletonData
open ActivePrefixStageHeadersData (Order)
open ActiveRepairLayoutRecordsData (Array)
open ActivePrefixStageFullCompose (three three_runs)
open Networks.Shared50ModularControl (prime)
variable {s : Shape}

abbrev privateCount := ActiveTargetHighestLayoutOriginalData.count
abbrev count := 66+privateCount

def producer (order : Order) := extend
  (extend (ActivePrefixStageHeadersPlaced.program (a := prime) order) 1) privateCount
def earlyConsumer := ActiveTargetHighestLayoutOriginalPlaced.earlierProgram focus focus_injective
def lateConsumerFor (m : ActivePrefixDirtyControlLoadProducer.Mode) :=
  ActiveTargetHighestLayoutOriginalPlaced.laterProgramFor m focus focus_injective
def lateConsumer := lateConsumerFor .pure
def cleanup := extend (extend ActivePrefixStageFullErase.program 1) privateCount

def earlierProgram := three (producer .early) earlyConsumer cleanup
def laterProgramFor (m : ActivePrefixDirtyControlLoadProducer.Mode) := three (producer .late) (lateConsumerFor m) cleanup
def laterProgram := laterProgramFor .pure

theorem later_composes (m : ActivePrefixDirtyControlLoadProducer.Mode)
    {B C E : ℕ} {P Q R S : TapePred count prime}
    (hp : HoareTime (producer .late) P Q B) (hs : HoareTime (lateConsumerFor m) Q R C)
    (hc : HoareTime cleanup R S E) : HoareTime (laterProgramFor m) P S (B+C+E+2) :=
  three_runs (M := producer .late) (N := lateConsumerFor m) (K := cleanup) hp hs hc

def bank (d : Inputs s) (x : Array s d.rows) := CleanSubbank.bank (s := privateCount) (original d x)

def earlyStageCost (d : Inputs s) (horder : d.stage.source.val<d.stage.target.val) :=
  ActiveTargetHighestLayoutOriginalRun.earlierCost
    (ActivePrefixLayoutHeadersGeometry.inputs s (params d) (earlyOffset d.stage) d.rows)
    (ActiveTargetHighestPairLayoutGeometry.early s (params d) (earlyOffset d.stage) d.rows
      (early_fits d.stage horder) (early_high_positive d.stage horder) (positive_H d.stage d.hG)
      d.hr (by have := d.hrecord; omega))
def lateStageCost (d : Inputs s) (horder : d.stage.target.val<d.stage.source.val) :=
  ActiveTargetHighestLayoutOriginalRun.laterCost
    (ActivePrefixLayoutHeadersGeometry.inputs s (params d) (lateOffset d.stage) d.rows)
    (ActiveTargetHighestPairLayoutGeometry.late s (params d) (lateOffset d.stage) d.rows
      (late_fits d.stage horder) (positive_before d.stage) (positive_H d.stage d.hG)
      d.hr (by have := d.hrecord; omega))
def earlyCost (d : Inputs s) (horder : d.stage.source.val<d.stage.target.val) :=
  ActivePrefixStageHeadersPlaced.cost .early d.stage d.rows+earlyStageCost d horder+
    ActivePrefixStageFullErase.cost .early d.toInputs+2
def lateCost (d : Inputs s) (horder : d.stage.target.val<d.stage.source.val) :=
  ActivePrefixStageHeadersPlaced.cost .late d.stage d.rows+lateStageCost d horder+
    ActivePrefixStageFullErase.cost .late d.toInputs+2

theorem earlier_runs (d : Inputs s) (x : Array s d.rows) (horder : d.stage.source.val<d.stage.target.val) :
    HoareTime earlierProgram (fun v => v=bank d x) (fun v => v=bank d (earlyResult d horder x)) (earlyCost d horder) := by
  have hp := hoare_extend_eq (hoare_extend_eq
    (ActivePrefixStageHeadersPlaced.runs (a := prime) .early d.stage d.rows d.hG horder)
    (ActivePrefixStageFullData.rawBank d.toInputs x)) (SharedBank.empty privateCount prime)
  have hs := ActiveTargetHighestLayoutOriginalGlobal.earlier_runs (ready .early d x) focus focus_injective
    s (params d) (earlyOffset d.stage) d.rows (early_fits d.stage horder)
    (early_high_positive d.stage horder) (positive_H d.stage d.hG) d.hr d.hrecord
    (ActivePrefixStageFullData.descriptors .early d.toInputs).hs x (sources .early d x)
    (ActivePrefixStageFullData.descriptors .early d.toInputs).hv (ActivePrefixStageFullData.descriptors .early d.toInputs).hc
  change HoareTime earlyConsumer
    (fun v => v=CleanSubbank.bank (s := privateCount) (ready .early d x))
    (fun v => v=CleanSubbank.bank (s := privateCount) (SharedPlacementAlphabet.setTape (ready .early d x)
      (focus 14) (ActiveTargetRotation.word (earlyResult d horder x)) 0)) (earlyStageCost d horder) at hs
  rw [caller_set] at hs
  have hc := hoare_extend_eq (ActivePrefixStageFullErase.runs .early d.toInputs (earlyResult d horder x))
    (SharedBank.empty privateCount prime)
  exact three_runs (M := producer .early) (N := earlyConsumer) (K := cleanup) hp hs hc

theorem later_runs (d : Inputs s) (x : Array s d.rows) (horder : d.stage.target.val<d.stage.source.val) :
    HoareTime laterProgram (fun v => v=bank d x) (fun v => v=bank d (lateResult d horder x)) (lateCost d horder) := by
  have hp := hoare_extend_eq (hoare_extend_eq
    (ActivePrefixStageHeadersPlaced.runs (a := prime) .late d.stage d.rows d.hG horder)
    (ActivePrefixStageFullData.rawBank d.toInputs x)) (SharedBank.empty privateCount prime)
  have hs := ActiveTargetHighestLayoutOriginalGlobal.later_runs (ready .late d x) focus focus_injective
    s (params d) (lateOffset d.stage) d.rows (late_fits d.stage horder)
    (positive_before d.stage) (positive_H d.stage d.hG) d.hr d.hrecord
    (ActivePrefixStageFullData.descriptors .late d.toInputs).hs x (sources .late d x)
    (ActivePrefixStageFullData.descriptors .late d.toInputs).hv (ActivePrefixStageFullData.descriptors .late d.toInputs).hc
  change HoareTime lateConsumer
    (fun v => v=CleanSubbank.bank (s := privateCount) (ready .late d x))
    (fun v => v=CleanSubbank.bank (s := privateCount) (SharedPlacementAlphabet.setTape (ready .late d x)
      (focus 14) (ActiveTargetRotation.word (lateResult d horder x)) 0)) (lateStageCost d horder) at hs
  rw [caller_set] at hs
  have hc := hoare_extend_eq (ActivePrefixStageFullErase.runs .late d.toInputs (lateResult d horder x))
    (SharedBank.empty privateCount prime)
  exact later_composes .pure hp hs hc

end
end IntegerMultBounds.Machine.ActivePrefixStageSingletonRun
