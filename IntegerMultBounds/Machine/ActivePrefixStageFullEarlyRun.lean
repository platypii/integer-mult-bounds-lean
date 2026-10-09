import IntegerMultBounds.Machine.ActivePrefixStageFullErase
import IntegerMultBounds.Machine.ActivePrefixStageFullCompose

/-! The complete early selected stage from original shape/node/slot words.
Synthesis, same-array action and consumer erasure are all physical and paid. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageFullEarlyRun
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters ActivePrefixStageGeometry
open ActivePrefixStageFullData
open ActiveRepairLayoutRecordsData (Array)
open ActivePrefixStageFullCompose (three three_runs)
open Networks.Shared50ModularControl (prime)
variable {s : Shape}

abbrev privateCount := ActiveRepairLayoutRecordsFullEarlyRun.count
abbrev count := 66+privateCount

def producer := extend (extend (ActivePrefixStageHeadersPlaced.program (a := prime) .early) 1) privateCount
def consumerFor (m : ActivePrefixDirtyControlLoadProducer.Mode) :=
  ActiveRepairLayoutRecordsFullEarlyPlaced.programFor m focus focus_injective
def cleanup := extend (extend ActivePrefixStageFullErase.program 1) privateCount
def surround {q : ℕ} (M : Program count q prime) := three producer M cleanup

def programFor (m : ActivePrefixDirtyControlLoadProducer.Mode) := surround (consumerFor m)
def program := programFor .pure

def bank (d : Inputs s) (x : Array s d.rows) := CleanSubbank.bank (s := privateCount) (original d x)
def stageCost (D : ℕ) (d : Inputs s) (horder : d.stage.source.val<d.stage.target.val) :=
  ActiveRepairLayoutRecordsFullEarlyRun.cost D s (parameters d.stage d.hG d.hGK) (earlyOffset d.stage) d.rows
    (early_fits d.stage horder) (early_high_positive d.stage horder) (positive_H d.stage d.hG) d.hr
    (by have := d.hrecord; omega)
def cost (D : ℕ) (d : Inputs s) (horder : d.stage.source.val<d.stage.target.val) :=
  ActivePrefixStageHeadersPlaced.cost .early d.stage d.rows+stageCost D d horder+
    ActivePrefixStageFullErase.cost .early d+2

theorem surround_runs {q B : ℕ} (M : Program count q prime) (d : Inputs s) (x y : Array s d.rows)
    (h : HoareTime M (fun v => v=CleanSubbank.bank (s := privateCount) (ready .early d x))
      (fun v => v=CleanSubbank.bank (s := privateCount) (ready .early d y)) B)
    (horder : ActivePrefixStageHeadersSchedule.Ordered .early d.stage) :
    HoareTime (surround M) (fun v => v=bank d x) (fun v => v=bank d y)
      (ActivePrefixStageHeadersPlaced.cost .early d.stage d.rows+B+ActivePrefixStageFullErase.cost .early d+2) := by
  have hp := hoare_extend_eq (hoare_extend_eq
    (ActivePrefixStageHeadersPlaced.runs (a := prime) .early d.stage d.rows d.hG horder) (rawBank d x))
    (SharedBank.empty privateCount prime)
  have hc := hoare_extend_eq (ActivePrefixStageFullErase.runs .early d y)
    (SharedBank.empty privateCount prime)
  exact three_runs (M := producer) (N := M) (K := cleanup) hp h hc

theorem runs_for (m : ActivePrefixDirtyControlLoadProducer.Mode) (d : Inputs s) (x y : Array s d.rows)
    (B : ℕ) (horder : d.stage.source.val<d.stage.target.val)
    (h : HoareTime (ActiveRepairLayoutRecordsFullEarlyRun.programFor m)
      (fun v => v=ActiveRepairLayoutRecordsFullEarlyRun.bank (descriptors .early d) x)
      (fun v => v=ActiveRepairLayoutRecordsFullEarlyRun.bank (descriptors .early d) y) B) :
    HoareTime (programFor m) (fun v => v=bank d x) (fun v => v=bank d y)
      (ActivePrefixStageHeadersPlaced.cost .early d.stage d.rows+B+ActivePrefixStageFullErase.cost .early d+2) := by
  have hs := ActiveRepairLayoutRecordsFullEarlyPlaced.runs_for m (ready .early d x)
    focus focus_injective (descriptors .early d) x y B (ready_sources .early d x) h
  have he : SharedPlacementAlphabet.setTape (ready .early d x) (focus 22)
      (ActiveTargetRotation.word y) 0=ready .early d y := caller_set d _ x y
  rw [he] at hs
  exact surround_runs (consumerFor m) d x y hs horder

theorem runs (d : Inputs s) (x : Array s d.rows) (horder : d.stage.source.val<d.stage.target.val)
    (hq3 : s.guard+3≤s.chunk)
    (hR : (ActiveRepairLayoutRecordsHeadersData.repair (descriptors .early d)).geom.addressBits+1≤s.payload)
    (D : ℕ) (hdensity : VaryingControlRepairDensity.earlyDensity s.chunk s.guard (d.stage.f-1)*
      ((ActiveRepairLayoutRecordsHeadersData.repair (descriptors .early d)).geom.addressBits+1)≤D) :
    HoareTime program (fun v => v=bank d x) (fun v => v=bank d (earlyResult d horder x)) (cost D d horder) :=
  runs_for .pure d x _ _ horder (ActiveRepairLayoutRecordsFullEarlyRun.runs (descriptors .early d) x
    (early_fits d.stage horder) (early_high_positive d.stage horder) (positive_H d.stage d.hG) hq3 hR D hdensity)

end
end IntegerMultBounds.Machine.ActivePrefixStageFullEarlyRun
