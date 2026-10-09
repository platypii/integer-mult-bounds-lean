import IntegerMultBounds.Machine.ActivePrefixStageInverseMachine
import IntegerMultBounds.Machine.ActivePrefixStageFullInverseData
import IntegerMultBounds.Machine.ActivePrefixStageFullBudget

/-! The same physical original-input stages implement recursive return. Every
reverse run pays synthesis/action/erasure; a round trip pays two runs and join. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageFullInverseRun
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters ActivePrefixStageGeometry
open ActivePrefixStageFullData
open ActiveRepairLayoutRecordsData (Array)
open ActivePrefixDirtyControlConjugationData (Kind)
variable {s : Shape}

namespace Early
def pairProgramFor (mode : ActivePrefixDirtyControlLoadProducer.Mode) := ActivePrefixStageInverseMachine.twice (ActivePrefixStageFullEarlyRun.programFor mode)
def pairProgram := pairProgramFor .pure

def ForwardSpecFor (mode : ActivePrefixDirtyControlLoadProducer.Mode) (D : ℕ) (d : Inputs s) (horder : d.stage.source.val<d.stage.target.val) : Prop :=
  ∀ x : Array s d.rows, HoareTime (ActivePrefixStageFullEarlyRun.programFor mode)
    (fun w => w=ActivePrefixStageFullEarlyRun.bank d x) (fun w => w=ActivePrefixStageFullEarlyRun.bank d (earlyResult d horder x)) (ActivePrefixStageFullEarlyRun.cost D d horder)
def UndoSpecFor (mode : ActivePrefixDirtyControlLoadProducer.Mode) (D : ℕ) (d : Inputs s) (horder : d.stage.source.val<d.stage.target.val) : Prop :=
  ∀ x : Array s d.rows, HoareTime (ActivePrefixStageFullEarlyRun.programFor mode)
    (fun w => w=ActivePrefixStageFullEarlyRun.bank d (earlyResult d horder x)) (fun w => w=ActivePrefixStageFullEarlyRun.bank d x) (ActivePrefixStageFullEarlyRun.cost D d horder)
def PairSpecFor (mode : ActivePrefixDirtyControlLoadProducer.Mode) (D : ℕ) (d : Inputs s) (horder : d.stage.source.val<d.stage.target.val) : Prop :=
  ∀ x : Array s d.rows, HoareTime (pairProgramFor mode)
    (fun w => w=ActivePrefixStageFullEarlyRun.bank d x) (fun w => w=ActivePrefixStageFullEarlyRun.bank d x) (2*ActivePrefixStageFullEarlyRun.cost D d horder+1)
def ForwardSpec := ForwardSpecFor (s := s) .pure
def UndoSpec := UndoSpecFor (s := s) .pure
def PairSpec := PairSpecFor (s := s) .pure

theorem undo_spec_for (mode : ActivePrefixDirtyControlLoadProducer.Mode) (D : ℕ) (d : Inputs s) (horder : d.stage.source.val<d.stage.target.val)
    (h : ForwardSpecFor mode D d horder) : UndoSpecFor mode D d horder :=
  ActivePrefixStageInverseMachine.undo (ActivePrefixStageFullEarlyRun.programFor mode) (ActivePrefixStageFullEarlyRun.bank d) (earlyResult d horder) (ActivePrefixStageFullInverseData.early d horder) h

theorem pair_spec_for (mode : ActivePrefixDirtyControlLoadProducer.Mode) (D : ℕ) (d : Inputs s) (horder : d.stage.source.val<d.stage.target.val)
    (h : ForwardSpecFor mode D d horder) : PairSpecFor mode D d horder :=
  ActivePrefixStageInverseMachine.pair (ActivePrefixStageFullEarlyRun.programFor mode) (ActivePrefixStageFullEarlyRun.bank d) (earlyResult d horder) (ActivePrefixStageFullInverseData.early d horder) h

theorem forward_spec_for (mode : ActivePrefixDirtyControlLoadProducer.Mode) (D : ℕ) (d : Inputs s) (horder : d.stage.source.val<d.stage.target.val)
    (h : ∀ x : Array s d.rows, HoareTime (ActiveRepairLayoutRecordsFullEarlyRun.programFor mode)
      (fun w => w=ActiveRepairLayoutRecordsFullEarlyRun.bank (descriptors .early d) x)
      (fun w => w=ActiveRepairLayoutRecordsFullEarlyRun.bank (descriptors .early d) (earlyResult d horder x))
      (ActivePrefixStageFullEarlyRun.stageCost D d horder)) : ForwardSpecFor mode D d horder :=
  fun x => ActivePrefixStageFullEarlyRun.runs_for mode d x _ _ horder (h x)

theorem forward_spec (D : ℕ) (d : Inputs s) (horder : d.stage.source.val<d.stage.target.val)
    (hq3 : s.guard+3≤s.chunk)
    (hR : (ActiveRepairLayoutRecordsHeadersData.repair (descriptors .early d)).geom.addressBits+1≤s.payload)
    (hDE : VaryingControlRepairDensity.earlyDensity s.chunk s.guard (d.stage.f-1)*
      ((ActiveRepairLayoutRecordsHeadersData.repair (descriptors .early d)).geom.addressBits+1)≤D) : ForwardSpec D d horder :=
  forward_spec_for .pure D d horder (fun x => ActiveRepairLayoutRecordsFullEarlyRun.runs (descriptors .early d) x
    (early_fits d.stage horder) (early_high_positive d.stage horder) (positive_H d.stage d.hG) hq3 hR D
    (by simpa only [parameters,ActiveRepairLayoutRecordsHeadersData.repair] using hDE))

theorem reverse_and_pair (D : ℕ) (d : Inputs s) (horder : d.stage.source.val<d.stage.target.val)
    (h : ForwardSpec D d horder) : UndoSpec D d horder ∧ PairSpec D d horder :=
  ⟨undo_spec_for .pure D d horder h,pair_spec_for .pure D d horder h⟩
end Early

namespace Late
def pairProgramFor (a b c e : Kind) (mode : ActivePrefixDirtyControlLoadProducer.Mode) := ActivePrefixStageInverseMachine.twice (ActivePrefixStageFullLateRun.programFor a b c e mode)
def pairProgram := pairProgramFor .tPure .tNegative .uPure .uNegative .pure

def ForwardSpecFor (a b c e : Kind) (mode : ActivePrefixDirtyControlLoadProducer.Mode) (D : ℕ) (d : Inputs s) (horder : d.stage.target.val<d.stage.source.val) (hn : 0<d.stage.f-1) (hb : 2≤s.guard) : Prop :=
  ∀ x : Array s d.rows, HoareTime (ActivePrefixStageFullLateRun.programFor a b c e mode)
    (fun w => w=ActivePrefixStageFullLateRun.bank d x) (fun w => w=ActivePrefixStageFullLateRun.bank d (lateResult d horder x)) (ActivePrefixStageFullLateRun.cost D d horder hn hb)
def UndoSpecFor (a b c e : Kind) (mode : ActivePrefixDirtyControlLoadProducer.Mode) (D : ℕ) (d : Inputs s) (horder : d.stage.target.val<d.stage.source.val) (hn : 0<d.stage.f-1) (hb : 2≤s.guard) : Prop :=
  ∀ x : Array s d.rows, HoareTime (ActivePrefixStageFullLateRun.programFor a b c e mode)
    (fun w => w=ActivePrefixStageFullLateRun.bank d (lateResult d horder x)) (fun w => w=ActivePrefixStageFullLateRun.bank d x) (ActivePrefixStageFullLateRun.cost D d horder hn hb)
def PairSpecFor (a b c e : Kind) (mode : ActivePrefixDirtyControlLoadProducer.Mode) (D : ℕ) (d : Inputs s) (horder : d.stage.target.val<d.stage.source.val) (hn : 0<d.stage.f-1) (hb : 2≤s.guard) : Prop :=
  ∀ x : Array s d.rows, HoareTime (pairProgramFor a b c e mode)
    (fun w => w=ActivePrefixStageFullLateRun.bank d x) (fun w => w=ActivePrefixStageFullLateRun.bank d x) (2*ActivePrefixStageFullLateRun.cost D d horder hn hb+1)
def ForwardSpec := ForwardSpecFor (s := s) .tPure .tNegative .uPure .uNegative .pure
def UndoSpec := UndoSpecFor (s := s) .tPure .tNegative .uPure .uNegative .pure
def PairSpec := PairSpecFor (s := s) .tPure .tNegative .uPure .uNegative .pure

theorem undo_spec_for (a b c e : Kind) (mode : ActivePrefixDirtyControlLoadProducer.Mode) (D : ℕ) (d : Inputs s) (horder : d.stage.target.val<d.stage.source.val) (hn : 0<d.stage.f-1) (hb : 2≤s.guard)
    (h : ForwardSpecFor a b c e mode D d horder hn hb) : UndoSpecFor a b c e mode D d horder hn hb :=
  ActivePrefixStageInverseMachine.undo (ActivePrefixStageFullLateRun.programFor a b c e mode) (ActivePrefixStageFullLateRun.bank d) (lateResult d horder) (ActivePrefixStageFullInverseData.late d horder) h

theorem pair_spec_for (a b c e : Kind) (mode : ActivePrefixDirtyControlLoadProducer.Mode) (D : ℕ) (d : Inputs s) (horder : d.stage.target.val<d.stage.source.val) (hn : 0<d.stage.f-1) (hb : 2≤s.guard)
    (h : ForwardSpecFor a b c e mode D d horder hn hb) : PairSpecFor a b c e mode D d horder hn hb :=
  ActivePrefixStageInverseMachine.pair (ActivePrefixStageFullLateRun.programFor a b c e mode) (ActivePrefixStageFullLateRun.bank d) (lateResult d horder) (ActivePrefixStageFullInverseData.late d horder) h

theorem forward_spec_for (a b c e : Kind) (mode : ActivePrefixDirtyControlLoadProducer.Mode) (D : ℕ) (d : Inputs s) (horder : d.stage.target.val<d.stage.source.val) (hn : 0<d.stage.f-1) (hb : 2≤s.guard)
    (h : ∀ x : Array s d.rows, HoareTime (ActiveRepairLayoutRecordsFullLateRun.programFor a b c e mode)
      (fun w => w=ActiveRepairLayoutRecordsFullLateRun.bank (descriptors .late d) x)
      (fun w => w=ActiveRepairLayoutRecordsFullLateRun.bank (descriptors .late d) (lateResult d horder x))
      (ActivePrefixStageFullLateRun.stageCost D d horder hn hb)) : ForwardSpecFor a b c e mode D d horder hn hb :=
  fun x => ActivePrefixStageFullLateRun.runs_for a b c e mode d x _ _ horder (h x)

theorem forward_spec (D : ℕ) (d : Inputs s) (horder : d.stage.target.val<d.stage.source.val) (hn : 0<d.stage.f-1) (hb : 2≤s.guard)
    (hq3 : s.guard+3≤s.chunk)
    (hR : (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair (descriptors .late d)).geom.addressBits+1≤s.payload)
    (hDE : VaryingControlRepairDensity.lateDensity s.chunk s.guard (d.stage.f-1)*
      ((ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair (descriptors .late d)).geom.addressBits+1)≤D) : ForwardSpec D d horder hn hb :=
  forward_spec_for .tPure .tNegative .uPure .uNegative .pure D d horder hn hb (fun x => ActiveRepairLayoutRecordsFullLateRun.runs (descriptors .late d) x
    (late_fits d.stage horder) hn hb (positive_before d.stage) (positive_H d.stage d.hG) hq3 hR D
    (by simpa only [parameters,ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair] using hDE))

theorem reverse_and_pair (D : ℕ) (d : Inputs s) (horder : d.stage.target.val<d.stage.source.val) (hn : 0<d.stage.f-1) (hb : 2≤s.guard)
    (h : ForwardSpec D d horder hn hb) : UndoSpec D d horder hn hb ∧ PairSpec D d horder hn hb :=
  ⟨undo_spec_for .tPure .tNegative .uPure .uNegative .pure D d horder hn hb h,pair_spec_for .tPure .tNegative .uPure .uNegative .pure D d horder hn hb h⟩
end Late

end
end IntegerMultBounds.Machine.ActivePrefixStageFullInverseRun
