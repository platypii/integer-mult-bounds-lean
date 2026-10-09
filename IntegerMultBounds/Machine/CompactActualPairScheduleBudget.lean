import IntegerMultBounds.Machine.CompactActualPairSchedule
import IntegerMultBounds.Machine.ActivePrefixStagePairBudget

/-! Actual scalar/global-row choices yield a uniform certified runtime for a
fixed literal binary schedule, including all pair backup, rewrite and restore
work. Its static instruction count is the only schedule factor. -/
namespace IntegerMultBounds.Machine.CompactActualPairScheduleBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open CompactActualStageGeometry CompactActualStageAllowance CompactActualStageInputs
open CompactActualPairSchedule
open CompactGlobalRowPadding CompactReservationCutoff
open Sizes
open ActiveRepairLayoutRecordsData (Array)
open ActivePrefixDirtyControlConjugationData (Kind)
open Networks.BinaryRowProgram (Op)
open ActivePrefixStagePairData (changePair)
open ActivePrefixStageRuntimeData (Packed)
open ActivePrefixStageInverseBudget (scale)

def BoundedSpecFor (a b c e : Kind) (m k r : ActivePrefixDirtyControlLoadProducer.Mode)
    (C : ℝ) {s : Shape} (input : ActivePrefixStageFullData.Inputs s)
    (ops : List (Op (Fin input.stage.slots))) : Prop :=
  ∃ hp : ∀ op,1 < input.stage.f → Packed (changePair input op) 1,
    (ActivePrefixStagePairSchedule.cost (ActivePrefixStagePairSchedule.stageCost 1 input hp) ops : ℝ)≤
      (ops.length : ℝ)*C*scale input ∧
    ∀ x : Array s input.rows,
      HoareTime (ActivePrefixStagePairSchedule.programFor a b c e m k r ops)
        (fun w => w=ActivePrefixStagePairRun.bank input x)
        (fun w => w=ActivePrefixStagePairRun.bank input (ActivePrefixStagePairSchedule.result input ops x))
        (ActivePrefixStagePairSchedule.cost (ActivePrefixStagePairSchedule.stageCost 1 input hp) ops)

def BoundedSpec (C : ℝ) {s : Shape} (input : ActivePrefixStageFullData.Inputs s)
    (ops : List (Op (Fin input.stage.slots))) : Prop :=
  BoundedSpecFor .tPure .tNegative .uPure .uNegative .pure .pure .pure C input ops

theorem bounded_for (a b c e : Kind) (m k r : ActivePrefixDirtyControlLoadProducer.Mode)
    (C : ℝ) {s : Shape} (input : ActivePrefixStageFullData.Inputs s)
    (ops : List (Op (Fin input.stage.slots))) (h : SpecFor a b c e m k r input ops)
    (hb : ∀ hp : ∀ op,1 < input.stage.f → Packed (changePair input op) 1,
      (ActivePrefixStagePairSchedule.cost (ActivePrefixStagePairSchedule.stageCost 1 input hp) ops : ℝ)≤
        (ops.length : ℝ)*C*scale input) : BoundedSpecFor a b c e m k r C input ops := by
  obtain ⟨hp,hrun⟩ := h
  exact ⟨hp,hb hp,hrun⟩

theorem uniform_bound : ∃ C : ℝ,0<C ∧
    ∀ (s : Shape) (input : ActivePrefixStageFullData.Inputs s) (ops : List (Op (Fin input.stage.slots))),
      Spec input ops → BoundedSpec C input ops := by
  obtain ⟨C,hC,hb⟩ := ActivePrefixStagePairBudget.schedule_uniform_bound 1
  refine ⟨C,hC,?_⟩
  intro s input ops h
  exact bounded_for .tPure .tNegative .uPure .uNegative .pure .pure .pure C input ops h
    (fun hp => hb s input hp ops)

theorem eventually_bounded (c m : ℕ) (hc : 2≤c) (hm : 2≤m) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in Filter.atTop,
    ∀ (D payload j : ℕ) (_hcut : cutoff c m n≤D) (_hD : D≤d n)
      (_hpayload : 6*b n*2^ℓ n≤payload) (_hj : j≤depth m (d n))
      (v : Stage (actualShape n c m D payload)) (ops : List (Op (Fin v.slots))),
      ∃ h : Ready (actualShape n c m D payload) v (rowsAt c m (d n) (K n) j),
        BoundedSpec C (inputs v (rowsAt c m (d n) (K n) j) h) ops := by
  obtain ⟨C,hC,hbound⟩ := uniform_bound
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ready_runs c m hc hm] with n hn
  intro D payload j hcut hD hpayload hj v ops
  obtain ⟨h,hrun⟩ := hn D payload j hcut hD hpayload hj v ops
  exact ⟨h,hbound (actualShape n c m D payload)
    (inputs v (rowsAt c m (d n) (K n) j) h) ops hrun⟩

end
end IntegerMultBounds.Machine.CompactActualPairScheduleBudget
