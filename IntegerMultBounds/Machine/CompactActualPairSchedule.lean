import IntegerMultBounds.Machine.CompactActualStageRuntime
import IntegerMultBounds.Machine.ActivePrefixStagePairSchedule

/-! The actual multiplier scalar and global-row choices supply density-one
allowances for every literal pair in a fixed binary schedule. No individual
stage allowance, runtime source order, or width branch is supplied. -/
namespace IntegerMultBounds.Machine.CompactActualPairSchedule
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open CompactActualStageGeometry CompactActualStageAllowance CompactActualStageInputs
open CompactGlobalRowPadding CompactReservationCutoff
open Sizes
open ActiveRepairLayoutRecordsData (Array)
open ActivePrefixDirtyControlConjugationData (Kind)
open Networks.BinaryRowProgram (Op)
open ActivePrefixStagePairData (changePair)
open ActivePrefixStageRuntimeData (Packed)

theorem ready_pair {s : Shape} (v : Stage s) (rows : ℕ) (h : Ready s v rows)
    (op : Op (Fin v.slots)) : Ready s (changePair (inputs v rows h) op).stage rows :=
  ⟨h.guardPositive,h.guardRoom,h.rowsPositive,h.recordAllowance,h.fullAddressAllowance,
    h.repairGuard,h.highestCapacity,positive_before _⟩

def SpecFor (a b c e : Kind) (m k r : ActivePrefixDirtyControlLoadProducer.Mode)
    {s : Shape} (input : ActivePrefixStageFullData.Inputs s)
    (ops : List (Op (Fin input.stage.slots))) : Prop :=
  ∃ hp : ∀ op,1 < input.stage.f → Packed (changePair input op) 1,
    ∀ x : Array s input.rows,
      HoareTime (ActivePrefixStagePairSchedule.programFor a b c e m k r ops)
        (fun w => w=ActivePrefixStagePairRun.bank input x)
        (fun w => w=ActivePrefixStagePairRun.bank input (ActivePrefixStagePairSchedule.result input ops x))
        (ActivePrefixStagePairSchedule.cost (ActivePrefixStagePairSchedule.stageCost 1 input hp) ops)

def Spec {s : Shape} (input : ActivePrefixStageFullData.Inputs s)
    (ops : List (Op (Fin input.stage.slots))) : Prop :=
  SpecFor .tPure .tNegative .uPure .uNegative .pure .pure .pure input ops

theorem spec_for (a b c e : Kind) (m k r : ActivePrefixDirtyControlLoadProducer.Mode)
    {s : Shape} (input : ActivePrefixStageFullData.Inputs s)
    (ops : List (Op (Fin input.stage.slots)))
    (hp : ∀ op,1 < input.stage.f → Packed (changePair input op) 1)
    (h : ∀ x : Array s input.rows,
      HoareTime (ActivePrefixStagePairSchedule.programFor a b c e m k r ops)
        (fun w => w=ActivePrefixStagePairRun.bank input x)
        (fun w => w=ActivePrefixStagePairRun.bank input (ActivePrefixStagePairSchedule.result input ops x))
        (ActivePrefixStagePairSchedule.cost (ActivePrefixStagePairSchedule.stageCost 1 input hp) ops)) :
    SpecFor a b c e m k r input ops := ⟨hp,h⟩

theorem spec {s : Shape} (input : ActivePrefixStageFullData.Inputs s)
    (ops : List (Op (Fin input.stage.slots)))
    (hp : ∀ op,1 < input.stage.f → Packed (changePair input op) 1) : Spec input ops :=
  spec_for .tPure .tNegative .uPure .uNegative .pure .pure .pure input ops hp
    (fun x => ActivePrefixStagePairSchedule.runs 1 input hp ops x)

theorem eventually_allowances (c m : ℕ) (hc : 2≤c) (hm : 2≤m) :
    ∀ᶠ n : ℕ in Filter.atTop,
    ∀ (D payload j : ℕ) (_hcut : cutoff c m n≤D) (_hD : D≤d n)
      (_hpayload : 6*b n*2^ℓ n≤payload)
      (v : Stage (actualShape n c m D payload))
      (h : Ready (actualShape n c m D payload) v (rowsAt c m (d n) (K n) j))
      (op : Op (Fin v.slots)),
      Packed (changePair (inputs v (rowsAt c m (d n) (K n) j) h) op) 1 := by
  filter_upwards [CompactActualStageRuntime.eventually_packed c m hc hm] with n hp
  intro D payload j hcut hD hpayload v h op
  exact hp D payload j hcut hD hpayload _ (ready_pair v _ h op)

theorem eventually_runs (c m : ℕ) (hc : 2≤c) (hm : 2≤m) :
    ∀ᶠ n : ℕ in Filter.atTop,
    ∀ (D payload j : ℕ) (_hcut : cutoff c m n≤D) (_hD : D≤d n)
      (_hpayload : 6*b n*2^ℓ n≤payload)
      (v : Stage (actualShape n c m D payload))
      (h : Ready (actualShape n c m D payload) v (rowsAt c m (d n) (K n) j))
      (ops : List (Op (Fin v.slots))),
      Spec (inputs v (rowsAt c m (d n) (K n) j) h) ops := by
  filter_upwards [eventually_allowances c m hc hm] with n hp
  intro D payload j hcut hD hpayload v h ops
  exact spec (inputs v (rowsAt c m (d n) (K n) j) h) ops
    (fun op _ => hp D payload j hcut hD hpayload v h op)

/-- The entire literal schedule, including saved-pair restoration after every
instruction, executes from original scalar/row conditions alone. -/
theorem eventually_ready_runs (c m : ℕ) (hc : 2≤c) (hm : 2≤m) :
    ∀ᶠ n : ℕ in Filter.atTop,
    ∀ (D payload j : ℕ) (_hcut : cutoff c m n≤D) (_hD : D≤d n)
      (_hpayload : 6*b n*2^ℓ n≤payload) (_hj : j≤depth m (d n))
      (v : Stage (actualShape n c m D payload)) (ops : List (Op (Fin v.slots))),
      ∃ h : Ready (actualShape n c m D payload) v (rowsAt c m (d n) (K n) j),
        Spec (inputs v (rowsAt c m (d n) (K n) j) h) ops := by
  filter_upwards [CompactActualStageGeometry.eventually_ready c m hc hm,eventually_runs c m hc hm] with n hr hrun
  intro D payload j hcut hD hpayload hj v ops
  let h := hr D payload j hcut hD hpayload hj v
  exact ⟨h,hrun D payload j hcut hD hpayload v h ops⟩

end
end IntegerMultBounds.Machine.CompactActualPairSchedule
