import IntegerMultBounds.Machine.ActivePrefixStageFullInverseRun
import IntegerMultBounds.Machine.ActivePrefixStageDispatchSelected
import IntegerMultBounds.Machine.ActivePrefixStageDispatchBudget

/-! Runtime source-order dispatch is physically self-inverse: running the
same compare/branch/erase program restores original words, array and flags. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageDispatchInverseRun
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs earlyResult lateResult)
open ActivePrefixStageDispatchData (result)
open ActivePrefixDirtyControlConjugationData (Kind)
open ActiveRepairLayoutRecordsData (Array)
variable {s : Shape}

def pairProgramFor (a b c e : Kind) (m n : ActivePrefixDirtyControlLoadProducer.Mode) :=
  ActivePrefixStageInverseMachine.twice (ActivePrefixStageDispatchRun.programFor a b c e m n)
def pairProgram := pairProgramFor .tPure .tNegative .uPure .uNegative .pure .pure

def ForwardSpecFor (a b c e : Kind) (m n : ActivePrefixDirtyControlLoadProducer.Mode)
    (D : ℕ) (d : Inputs s) (hn : 0<d.stage.f-1) (hb : 2≤s.guard) : Prop :=
  ∀ x : Array s d.rows, HoareTime (ActivePrefixStageDispatchRun.programFor a b c e m n)
    (fun w => w=ActivePrefixStageDispatchRun.bank d x)
    (fun w => w=ActivePrefixStageDispatchRun.bank d (result d x)) (ActivePrefixStageDispatchRun.cost D d hn hb)
def UndoSpecFor (a b c e : Kind) (m n : ActivePrefixDirtyControlLoadProducer.Mode)
    (D : ℕ) (d : Inputs s) (hn : 0<d.stage.f-1) (hb : 2≤s.guard) : Prop :=
  ∀ x : Array s d.rows, HoareTime (ActivePrefixStageDispatchRun.programFor a b c e m n)
    (fun w => w=ActivePrefixStageDispatchRun.bank d (result d x))
    (fun w => w=ActivePrefixStageDispatchRun.bank d x) (ActivePrefixStageDispatchRun.cost D d hn hb)
def PairSpecFor (a b c e : Kind) (m n : ActivePrefixDirtyControlLoadProducer.Mode)
    (D : ℕ) (d : Inputs s) (hn : 0<d.stage.f-1) (hb : 2≤s.guard) : Prop :=
  ∀ x : Array s d.rows, HoareTime (pairProgramFor a b c e m n)
    (fun w => w=ActivePrefixStageDispatchRun.bank d x)
    (fun w => w=ActivePrefixStageDispatchRun.bank d x) (2*ActivePrefixStageDispatchRun.cost D d hn hb+1)
def ForwardSpec := ForwardSpecFor (s := s) .tPure .tNegative .uPure .uNegative .pure .pure
def UndoSpec := UndoSpecFor (s := s) .tPure .tNegative .uPure .uNegative .pure .pure
def PairSpec := PairSpecFor (s := s) .tPure .tNegative .uPure .uNegative .pure .pure

theorem undo_spec_for (a b c e : Kind) (m n : ActivePrefixDirtyControlLoadProducer.Mode)
    (D : ℕ) (d : Inputs s) (hn : 0<d.stage.f-1) (hb : 2≤s.guard)
    (h : ForwardSpecFor a b c e m n D d hn hb) : UndoSpecFor a b c e m n D d hn hb :=
  ActivePrefixStageInverseMachine.undo (ActivePrefixStageDispatchRun.programFor a b c e m n)
    (ActivePrefixStageDispatchRun.bank d) (result d) (ActivePrefixStageDispatchSelected.involutive d) h

theorem pair_spec_for (a b c e : Kind) (m n : ActivePrefixDirtyControlLoadProducer.Mode)
    (D : ℕ) (d : Inputs s) (hn : 0<d.stage.f-1) (hb : 2≤s.guard)
    (h : ForwardSpecFor a b c e m n D d hn hb) : PairSpecFor a b c e m n D d hn hb :=
  ActivePrefixStageInverseMachine.pair (ActivePrefixStageDispatchRun.programFor a b c e m n)
    (ActivePrefixStageDispatchRun.bank d) (result d) (ActivePrefixStageDispatchSelected.involutive d) h

theorem forward_spec_for (a b c e : Kind) (m n : ActivePrefixDirtyControlLoadProducer.Mode)
    (D : ℕ) (d : Inputs s) (hn : 0<d.stage.f-1) (hb : 2≤s.guard)
    (hE : ∀ ho : d.stage.source.val<d.stage.target.val,
      ActivePrefixStageFullInverseRun.Early.ForwardSpecFor n D d ho)
    (hL : ∀ ho : d.stage.target.val<d.stage.source.val,
      ActivePrefixStageFullInverseRun.Late.ForwardSpecFor a b c e m D d ho hn hb) :
    ForwardSpecFor a b c e m n D d hn hb := by
  intro x
  by_cases h : d.stage.source.val<d.stage.target.val
  · have hr : result d x=earlyResult d h x := dite_eq_left h
    have hc : ActivePrefixStageDispatchRun.cost D d hn hb=ActivePrefixStageOrderCompare.cost d.stage+
        ActivePrefixStageFullEarlyRun.cost D d h+4 := dite_eq_left h
    have hh := ActivePrefixStageDispatchRun.early_dispatch a b c e m n d x _ _ h (hE h x)
    exact hh.consequence (fun _ hv => hv)
      (fun _ hv => hv.trans (congrArg (ActivePrefixStageDispatchRun.bank d) hr.symm)) hc.symm.le
  · have ho := ActivePrefixStageOrderCompare.late_of_not_early d.stage h
    have hr : result d x=lateResult d ho x := dite_eq_right h
    have hc : ActivePrefixStageDispatchRun.cost D d hn hb=ActivePrefixStageOrderCompare.cost d.stage+
        ActivePrefixStageFullLateRun.cost D d ho hn hb+4 := dite_eq_right h
    have hh := ActivePrefixStageDispatchRun.late_dispatch a b c e m n d x _ _ ho (hL ho x)
    exact hh.consequence (fun _ hv => hv)
      (fun _ hv => hv.trans (congrArg (ActivePrefixStageDispatchRun.bank d) hr.symm)) hc.symm.le

theorem forward_spec (D : ℕ) (d : Inputs s) (hn : 0<d.stage.f-1) (hb : 2≤s.guard)
    (hq3 : s.guard+3≤s.chunk)
    (hRE : (ActiveRepairLayoutRecordsHeadersData.repair (ActivePrefixStageFullData.descriptors .early d)).geom.addressBits+1≤s.payload)
    (hRL : (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair (ActivePrefixStageFullData.descriptors .late d)).geom.addressBits+1≤s.payload)
    (hDE : VaryingControlRepairDensity.earlyDensity s.chunk s.guard (d.stage.f-1)*
      ((ActiveRepairLayoutRecordsHeadersData.repair (ActivePrefixStageFullData.descriptors .early d)).geom.addressBits+1)≤D)
    (hDL : VaryingControlRepairDensity.lateDensity s.chunk s.guard (d.stage.f-1)*
      ((ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair (ActivePrefixStageFullData.descriptors .late d)).geom.addressBits+1)≤D) :
    ForwardSpec D d hn hb :=
  forward_spec_for .tPure .tNegative .uPure .uNegative .pure .pure D d hn hb
    (fun ho => ActivePrefixStageFullInverseRun.Early.forward_spec D d ho hq3 hRE hDE)
    (fun ho => ActivePrefixStageFullInverseRun.Late.forward_spec D d ho hn hb hq3 hRL hDL)

theorem reverse_and_pair (D : ℕ) (d : Inputs s) (hn : 0<d.stage.f-1) (hb : 2≤s.guard)
    (h : ForwardSpec D d hn hb) : UndoSpec D d hn hb ∧ PairSpec D d hn hb :=
  ⟨undo_spec_for .tPure .tNegative .uPure .uNegative .pure .pure D d hn hb h,
    pair_spec_for .tPure .tNegative .uPure .uNegative .pure .pure D d hn hb h⟩

end
end IntegerMultBounds.Machine.ActivePrefixStageDispatchInverseRun
