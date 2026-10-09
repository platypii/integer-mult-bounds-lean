import IntegerMultBounds.Machine.ActivePrefixStagePairSchedule
import IntegerMultBounds.Machine.ActivePrefixStageRuntimeInverseRun
import IntegerMultBounds.Machine.ActivePrefixStagePairBudget

/-! Reverse the actual literal stage list to undo a basis-word execution.
Original pair restoration in every instruction makes the common caller bank
identical throughout; the reverse costs exactly the forward charged sum. -/
namespace IntegerMultBounds.Machine.ActivePrefixStagePairInverse
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActiveRepairLayoutRecordsData (Array)
open ActivePrefixStagePairSchedule (result cost stageCost)
open ActivePrefixStagePairRun (action bank)
open Networks.BinaryRowProgram (Op)
open ActivePrefixDirtyControlConjugationData (Kind)
variable {s : Shape}

theorem action_involutive (d : Inputs s) (op : Op (Fin d.stage.slots)) : Function.Involutive (action d op) :=
  ActivePrefixStageRuntimeInverseRun.involutive (ActivePrefixStagePairData.changePair d op)

theorem result_append (d : Inputs s) (u v : List (Op (Fin d.stage.slots))) (x : Array s d.rows) :
    result d (u++v) x=result d v (result d u x) := by
  induction u generalizing x with
  | nil => rfl
  | cons op ops ih => exact ih (action d op x)

theorem reverse_restores (d : Inputs s) (ops : List (Op (Fin d.stage.slots))) (x : Array s d.rows) :
    result d ops.reverse (result d ops x)=x := by
  induction ops generalizing x with
  | nil => rfl
  | cons op ops ih =>
    rw [List.reverse_cons,result_append]
    change action d op (result d ops.reverse (result d ops (action d op x)))=x
    rw [ih]
    exact action_involutive d op x

theorem cost_reverse {M : ℕ} (B : Op (Fin M) → ℕ) (ops : List (Op (Fin M))) :
    cost B ops.reverse=cost B ops := by simp [cost,List.map_reverse]

theorem undo_for (a b c e : Kind) (m n r : ActivePrefixDirtyControlLoadProducer.Mode)
    (d : Inputs s) (B : Op (Fin d.stage.slots) → ℕ)
    (hb : ∀ op x, HoareTime (ActivePrefixStagePairRun.programFor op a b c e m n r)
      (fun w => w=bank d x) (fun w => w=bank d (action d op x)) (B op))
    (ops : List (Op (Fin d.stage.slots))) (x : Array s d.rows) :
    HoareTime (ActivePrefixStagePairSchedule.programFor a b c e m n r ops.reverse)
      (fun w => w=bank d (result d ops x)) (fun w => w=bank d x) (cost B ops) := by
  have h := ActivePrefixStagePairSchedule.runs_for a b c e m n r d B hb ops.reverse (result d ops x)
  rw [reverse_restores,cost_reverse] at h
  exact h

def pairFor (a b c e : Kind) (m n r : ActivePrefixDirtyControlLoadProducer.Mode)
    {M : ℕ} (ops : List (Op (Fin M))) :=
  seq (ActivePrefixStagePairSchedule.programFor a b c e m n r ops)
    (ActivePrefixStagePairSchedule.programFor a b c e m n r ops.reverse)

theorem pair_runs_for (a b c e : Kind) (m n r : ActivePrefixDirtyControlLoadProducer.Mode)
    (d : Inputs s) (B : Op (Fin d.stage.slots) → ℕ)
    (hb : ∀ op x, HoareTime (ActivePrefixStagePairRun.programFor op a b c e m n r)
      (fun w => w=bank d x) (fun w => w=bank d (action d op x)) (B op))
    (ops : List (Op (Fin d.stage.slots))) (x : Array s d.rows) :
    HoareTime (pairFor a b c e m n r ops) (fun w => w=bank d x) (fun w => w=bank d x)
      (2*cost B ops+1) :=
  ((ActivePrefixStagePairSchedule.runs_for a b c e m n r d B hb ops x).seq
    (undo_for a b c e m n r d B hb ops x)).consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem undo_runs (D : ℕ) (d : Inputs s)
    (hp : ∀ op,1<d.stage.f → ActivePrefixStageRuntimeData.Packed (ActivePrefixStagePairData.changePair d op) D)
    (ops : List (Op (Fin d.stage.slots))) (x : Array s d.rows) :
    HoareTime (ActivePrefixStagePairSchedule.program ops.reverse)
      (fun w => w=bank d (result d ops x)) (fun w => w=bank d x) (cost (stageCost D d hp) ops) :=
  undo_for .tPure .tNegative .uPure .uNegative .pure .pure .pure d (stageCost D d hp)
    (fun op x => ActivePrefixStagePairRun.runs D d op x (hp op)) ops x

theorem pair_runs (D : ℕ) (d : Inputs s)
    (hp : ∀ op,1<d.stage.f → ActivePrefixStageRuntimeData.Packed (ActivePrefixStagePairData.changePair d op) D)
    (ops : List (Op (Fin d.stage.slots))) (x : Array s d.rows) :
    HoareTime (pairFor .tPure .tNegative .uPure .uNegative .pure .pure .pure ops)
      (fun w => w=bank d x) (fun w => w=bank d x) (2*cost (stageCost D d hp) ops+1) :=
  pair_runs_for .tPure .tNegative .uPure .uNegative .pure .pure .pure d (stageCost D d hp)
    (fun op x => ActivePrefixStagePairRun.runs D d op x (hp op)) ops x

/-- The joins in an empty or nonempty word's round trip are all paid. -/
theorem uniform_pair_bound (D : ℕ) : ∃ C : ℝ,0<C ∧
    ∀ (s : Shape) (d : Inputs s)
      (hp : ∀ op,1<d.stage.f → ActivePrefixStageRuntimeData.Packed (ActivePrefixStagePairData.changePair d op) D)
      (ops : List (Op (Fin d.stage.slots))),
      ((2*cost (stageCost D d hp) ops+1 : ℕ) : ℝ)≤
        ((ops.length : ℝ)*C+1)*ActivePrefixStageInverseBudget.scale d := by
  obtain ⟨C,hC,h⟩ := ActivePrefixStagePairBudget.schedule_uniform_bound D
  refine ⟨2*C,by positivity,?_⟩
  intro s d hp ops
  have hb := h s d hp ops
  have hu := ActivePrefixStageInverseBudget.one_le_scale d
  push_cast
  nlinarith only [hb,hu]

end
end IntegerMultBounds.Machine.ActivePrefixStagePairInverse
