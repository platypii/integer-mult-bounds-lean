import IntegerMultBounds.Machine.ActivePrefixStageFullErase
import IntegerMultBounds.Machine.ActivePrefixStageFullCompose

/-! Complete later selected action from original node/slot geometry, including
physical descriptor preparation and erasure around the unchanged raw array. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageFullLateRun
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters ActivePrefixStageGeometry
open ActivePrefixStageFullData
open ActiveRepairLayoutRecordsData (Array)
open ActivePrefixStageFullCompose (three three_runs)
open ActivePrefixDirtyControlConjugationData (Kind)
open Networks.Shared50ModularControl (prime)
variable {s : Shape}

abbrev privateCount := ActiveRepairLayoutRecordsFullLateRun.count
abbrev count := 66+privateCount

def producer := extend (extend (ActivePrefixStageHeadersPlaced.program (a := prime) .late) 1) privateCount
def consumerFor (a b c e : Kind) (m : ActivePrefixDirtyControlLoadProducer.Mode) :=
  ActiveRepairLayoutRecordsFullLatePlaced.programFor a b c e m focus focus_injective
def cleanup := extend (extend ActivePrefixStageFullErase.program 1) privateCount
def surround {q : ℕ} (M : Program count q prime) := three producer M cleanup

def programFor (a b c e : Kind) (m : ActivePrefixDirtyControlLoadProducer.Mode) :=
  surround (consumerFor a b c e m)
def program := programFor .tPure .tNegative .uPure .uNegative .pure

def bank (d : Inputs s) (x : Array s d.rows) := CleanSubbank.bank (s := privateCount) (original d x)
def stageCost (D : ℕ) (d : Inputs s) (horder : d.stage.target.val<d.stage.source.val)
    (hn : 0<d.stage.f-1) (hb : 2≤s.guard) :=
  ActiveRepairLayoutRecordsFullLateRun.cost D (late_fits d.stage horder) hn hb (descriptors .late d)
    (positive_before d.stage) (positive_H d.stage d.hG)
def cost (D : ℕ) (d : Inputs s) (horder : d.stage.target.val<d.stage.source.val)
    (hn : 0<d.stage.f-1) (hb : 2≤s.guard) :=
  ActivePrefixStageHeadersPlaced.cost .late d.stage d.rows+stageCost D d horder hn hb+
    ActivePrefixStageFullErase.cost .late d+2

theorem surround_runs {q B : ℕ} (M : Program count q prime) (d : Inputs s) (x y : Array s d.rows)
    (h : HoareTime M (fun v => v=CleanSubbank.bank (s := privateCount) (ready .late d x))
      (fun v => v=CleanSubbank.bank (s := privateCount) (ready .late d y)) B)
    (horder : ActivePrefixStageHeadersSchedule.Ordered .late d.stage) :
    HoareTime (surround M) (fun v => v=bank d x) (fun v => v=bank d y)
      (ActivePrefixStageHeadersPlaced.cost .late d.stage d.rows+B+ActivePrefixStageFullErase.cost .late d+2) := by
  have hp := hoare_extend_eq (hoare_extend_eq
    (ActivePrefixStageHeadersPlaced.runs (a := prime) .late d.stage d.rows d.hG horder) (rawBank d x))
    (SharedBank.empty privateCount prime)
  have hc := hoare_extend_eq (ActivePrefixStageFullErase.runs .late d y)
    (SharedBank.empty privateCount prime)
  exact three_runs (M := producer) (N := M) (K := cleanup) hp h hc

theorem runs_for (a b c e : Kind) (m : ActivePrefixDirtyControlLoadProducer.Mode)
    (d : Inputs s) (x y : Array s d.rows) (B : ℕ) (horder : d.stage.target.val<d.stage.source.val)
    (h : HoareTime (ActiveRepairLayoutRecordsFullLateRun.programFor a b c e m)
      (fun v => v=ActiveRepairLayoutRecordsFullLateRun.bank (descriptors .late d) x)
      (fun v => v=ActiveRepairLayoutRecordsFullLateRun.bank (descriptors .late d) y) B) :
    HoareTime (programFor a b c e m) (fun v => v=bank d x) (fun v => v=bank d y)
      (ActivePrefixStageHeadersPlaced.cost .late d.stage d.rows+B+ActivePrefixStageFullErase.cost .late d+2) := by
  have hs := ActiveRepairLayoutRecordsFullLatePlaced.placed_runs a b c e m (ready .late d x)
    focus focus_injective (descriptors .late d) x y B (late_sources d x) h
  have he : SharedPlacementAlphabet.setTape (ready .late d x) (focus 22)
      (ActiveTargetRotation.word y) 0=ready .late d y := caller_set d _ x y
  rw [he] at hs
  exact surround_runs (consumerFor a b c e m) d x y hs horder

theorem runs (d : Inputs s) (x : Array s d.rows) (horder : d.stage.target.val<d.stage.source.val)
    (hn : 0<d.stage.f-1) (hb : 2≤s.guard) (hq3 : s.guard+3≤s.chunk)
    (hR : (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair (descriptors .late d)).geom.addressBits+1≤s.payload)
    (D : ℕ) (hdensity : VaryingControlRepairDensity.lateDensity s.chunk s.guard (d.stage.f-1)*
      ((ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair (descriptors .late d)).geom.addressBits+1)≤D) :
    HoareTime program (fun v => v=bank d x) (fun v => v=bank d (lateResult d horder x))
      (cost D d horder hn hb) :=
  runs_for .tPure .tNegative .uPure .uNegative .pure d x _ _ horder
    (ActiveRepairLayoutRecordsFullLateRun.runs (descriptors .late d) x (late_fits d.stage horder) hn hb
      (positive_before d.stage) (positive_H d.stage d.hG) hq3 hR D hdensity)

end
end IntegerMultBounds.Machine.ActivePrefixStageFullLateRun
