import IntegerMultBounds.Machine.CompactActualPairSchedule
import IntegerMultBounds.Machine.ActivePrefixStagePairInverse

/-! Actual multiplier choices supply a complete physical reverse and round
trip for every literal binary word, including the empty word. No individual
readiness, allowance, direction or width-case proof is supplied. -/
namespace IntegerMultBounds.Machine.CompactActualPairInverse
noncomputable section
open ActivePrefixStageParameters
open CompactActualStageGeometry CompactActualStageAllowance CompactActualStageInputs
open CompactGlobalRowPadding CompactReservationCutoff Sizes
open ActiveRepairLayoutRecordsData (Array)
open Networks.BinaryRowProgram (Op)
open ActivePrefixStagePairSchedule (result cost stageCost)
open ActivePrefixStagePairRun (bank)
open ActivePrefixStageRuntimeData (Packed)
open ActivePrefixStagePairData (changePair)
open CompactGadgetReservationShape (Shape)
open ActivePrefixDirtyControlConjugationData (Kind)

def SpecFor (a b c e : Kind) (m k r : ActivePrefixDirtyControlLoadProducer.Mode) {s : Shape} (input : ActivePrefixStageFullData.Inputs s)
    (ops : List (Op (Fin input.stage.slots))) : Prop :=
  ∃ hp : ∀ op,1 < input.stage.f → Packed (changePair input op) 1,
    ∀ x : Array s input.rows,
      HoareTime (ActivePrefixStagePairSchedule.programFor a b c e m k r ops.reverse)
        (fun w => w=bank input (result input ops x)) (fun w => w=bank input x)
        (cost (stageCost 1 input hp) ops) ∧
      HoareTime (ActivePrefixStagePairInverse.pairFor a b c e m k r ops)
        (fun w => w=bank input x) (fun w => w=bank input x)
        (2*cost (stageCost 1 input hp) ops+1)

def Spec {s : Shape} (input : ActivePrefixStageFullData.Inputs s)
    (ops : List (Op (Fin input.stage.slots))) :=
  SpecFor .tPure .tNegative .uPure .uNegative .pure .pure .pure input ops

theorem spec_for (a b c e : Kind) (m k r : ActivePrefixDirtyControlLoadProducer.Mode)
    {s : Shape} (input : ActivePrefixStageFullData.Inputs s)
    (ops : List (Op (Fin input.stage.slots)))
    (hp : ∀ op,1 < input.stage.f → Packed (changePair input op) 1)
    (h : ∀ op x, HoareTime (ActivePrefixStagePairRun.programFor op a b c e m k r)
      (fun w => w=bank input x) (fun w => w=bank input (ActivePrefixStagePairRun.action input op x))
      (stageCost 1 input hp op)) : SpecFor a b c e m k r input ops :=
  ⟨hp,fun x => ⟨ActivePrefixStagePairInverse.undo_for a b c e m k r input _ h ops x,
    ActivePrefixStagePairInverse.pair_runs_for a b c e m k r input _ h ops x⟩⟩

theorem spec {s : Shape} (input : ActivePrefixStageFullData.Inputs s)
    (ops : List (Op (Fin input.stage.slots)))
    (hp : ∀ op,1 < input.stage.f → Packed (changePair input op) 1) : Spec input ops :=
  spec_for .tPure .tNegative .uPure .uNegative .pure .pure .pure input ops hp
    (fun op x => ActivePrefixStagePairRun.runs 1 input op x (hp op))

theorem eventually_runs_for (a b' c' e : Kind)
    (mode k r : ActivePrefixDirtyControlLoadProducer.Mode)
    (c m : ℕ) (hc : 2≤c) (hm : 2≤m)
    (hspec : ∀ (s : Shape) (input : ActivePrefixStageFullData.Inputs s)
      (ops : List (Op (Fin input.stage.slots)))
      (_hp : ∀ op,1 < input.stage.f → Packed (changePair input op) 1),
      SpecFor a b' c' e mode k r input ops) :
    ∀ᶠ n : ℕ in Filter.atTop,
    ∀ (D payload j : ℕ) (_hcut : cutoff c m n≤D) (_hD : D≤d n)
      (_hpayload : 6*b n*2^ℓ n≤payload) (_hj : j≤depth m (d n))
      (input : ActivePrefixStageFullData.Inputs (actualShape n c m D payload))
      (_hrows : input.rows=rowsAt c m (d n) (K n) j)
      (ops : List (Op (Fin input.stage.slots))),
      SpecFor a b' c' e mode k r input ops := by
  filter_upwards [CompactActualStageGeometry.eventually_ready c m hc hm,
    CompactActualPairSchedule.eventually_allowances c m hc hm] with n hr ha
  intro D payload j hcut hD hpayload hj input hrows ops
  let h := hr D payload j hcut hD hpayload hj input.stage
  apply hspec _ input ops
  intro op _
  have hh := ha D payload j hcut hD hpayload input.stage h op
  have hpair : changePair (inputs input.stage (rowsAt c m (d n) (K n) j) h) op=changePair input op := by
    cases input
    cases hrows
    rfl
  rwa [hpair] at hh

theorem eventually_runs (c m : ℕ) (hc : 2≤c) (hm : 2≤m) :
    ∀ᶠ n : ℕ in Filter.atTop,
    ∀ (D payload j : ℕ) (_hcut : cutoff c m n≤D) (_hD : D≤d n)
      (_hpayload : 6*b n*2^ℓ n≤payload) (_hj : j≤depth m (d n))
      (input : ActivePrefixStageFullData.Inputs (actualShape n c m D payload))
      (_hrows : input.rows=rowsAt c m (d n) (K n) j)
      (ops : List (Op (Fin input.stage.slots))), Spec input ops :=
  eventually_runs_for .tPure .tNegative .uPure .uNegative .pure .pure .pure c m hc hm
    (fun _ input ops hp => spec input ops hp)

end
end IntegerMultBounds.Machine.CompactActualPairInverse
