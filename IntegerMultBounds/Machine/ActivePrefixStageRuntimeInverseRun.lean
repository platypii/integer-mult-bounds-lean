import IntegerMultBounds.Machine.ActivePrefixStageSingletonInverseData
import IntegerMultBounds.Machine.ActivePrefixStageDispatchInverseRun
import IntegerMultBounds.Machine.ActivePrefixStageRuntimeRun

/-! The complete fixed width-and-direction program executes its own inverse.
Both runtime flags and every private tape are restored on each return. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageRuntimeInverseRun
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageRuntimeData (Packed result cost)
open ActivePrefixDirtyControlConjugationData (Kind)
open ActiveRepairLayoutRecordsData (Array)
variable {s : Shape}

theorem involutive (d : Inputs s) : Function.Involutive (result d) := by
  intro x
  by_cases h : 1<d.stage.f
  · simp only [result,dite_eq_left h]
    exact ActivePrefixStageDispatchSelected.involutive d x
  · simp only [result,dite_eq_right h]
    exact ActivePrefixStageSingletonInverseData.dispatch (ActivePrefixStageRuntimeData.singleton d h) x

def pairProgramFor (a b c e : Kind) (m n r : ActivePrefixDirtyControlLoadProducer.Mode) :=
  ActivePrefixStageInverseMachine.twice (ActivePrefixStageRuntimeProgram.programFor a b c e m n r)
def pairProgram := pairProgramFor .tPure .tNegative .uPure .uNegative .pure .pure .pure

def ForwardSpecFor (a b c e : Kind) (m n r : ActivePrefixDirtyControlLoadProducer.Mode)
    (D : ℕ) (d : Inputs s) (hp : 1<d.stage.f → Packed d D) : Prop :=
  ∀ x : Array s d.rows, HoareTime (ActivePrefixStageRuntimeProgram.programFor a b c e m n r)
    (fun w => w=ActivePrefixStageRuntimeProgram.bank d x)
    (fun w => w=ActivePrefixStageRuntimeProgram.bank d (result d x)) (cost D d hp)
def UndoSpecFor (a b c e : Kind) (m n r : ActivePrefixDirtyControlLoadProducer.Mode)
    (D : ℕ) (d : Inputs s) (hp : 1<d.stage.f → Packed d D) : Prop :=
  ∀ x : Array s d.rows, HoareTime (ActivePrefixStageRuntimeProgram.programFor a b c e m n r)
    (fun w => w=ActivePrefixStageRuntimeProgram.bank d (result d x))
    (fun w => w=ActivePrefixStageRuntimeProgram.bank d x) (cost D d hp)
def PairSpecFor (a b c e : Kind) (m n r : ActivePrefixDirtyControlLoadProducer.Mode)
    (D : ℕ) (d : Inputs s) (hp : 1<d.stage.f → Packed d D) : Prop :=
  ∀ x : Array s d.rows, HoareTime (pairProgramFor a b c e m n r)
    (fun w => w=ActivePrefixStageRuntimeProgram.bank d x)
    (fun w => w=ActivePrefixStageRuntimeProgram.bank d x) (2*cost D d hp+1)
def ForwardSpec := ForwardSpecFor (s := s) .tPure .tNegative .uPure .uNegative .pure .pure .pure
def UndoSpec := UndoSpecFor (s := s) .tPure .tNegative .uPure .uNegative .pure .pure .pure
def PairSpec := PairSpecFor (s := s) .tPure .tNegative .uPure .uNegative .pure .pure .pure

theorem undo_spec_for (a b c e : Kind) (m n r : ActivePrefixDirtyControlLoadProducer.Mode)
    (D : ℕ) (d : Inputs s) (hp : 1<d.stage.f → Packed d D)
    (h : ForwardSpecFor a b c e m n r D d hp) : UndoSpecFor a b c e m n r D d hp :=
  ActivePrefixStageInverseMachine.undo (ActivePrefixStageRuntimeProgram.programFor a b c e m n r)
    (ActivePrefixStageRuntimeProgram.bank d) (result d) (involutive d) h

theorem pair_spec_for (a b c e : Kind) (m n r : ActivePrefixDirtyControlLoadProducer.Mode)
    (D : ℕ) (d : Inputs s) (hp : 1<d.stage.f → Packed d D)
    (h : ForwardSpecFor a b c e m n r D d hp) : PairSpecFor a b c e m n r D d hp :=
  ActivePrefixStageInverseMachine.pair (ActivePrefixStageRuntimeProgram.programFor a b c e m n r)
    (ActivePrefixStageRuntimeProgram.bank d) (result d) (involutive d) h

theorem reverse_and_pair (D : ℕ) (d : Inputs s) (hp : 1<d.stage.f → Packed d D)
    (h : ForwardSpec D d hp) : UndoSpec D d hp ∧ PairSpec D d hp :=
  ⟨undo_spec_for .tPure .tNegative .uPure .uNegative .pure .pure .pure D d hp h,
   pair_spec_for .tPure .tNegative .uPure .uNegative .pure .pure .pure D d hp h⟩

end
end IntegerMultBounds.Machine.ActivePrefixStageRuntimeInverseRun
