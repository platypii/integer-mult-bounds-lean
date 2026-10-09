import IntegerMultBounds.Machine.CompactActualStageInputs
import IntegerMultBounds.Machine.ActivePrefixStageRuntimeSelected

/-! Actual scalar choices, cutoff and global row padding supply every premise
of the fixed width-and-direction stage at density one. Every positive runtime
width is covered, including singleton stages, with no supplied branch. -/
namespace IntegerMultBounds.Machine.CompactActualStageRuntime
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open CompactActualStageGeometry CompactActualStageAllowance CompactActualStageInputs
open CompactGlobalRowPadding CompactReservationCutoff
open Sizes
open ActiveRepairLayoutRecordsData (Array)
open ActivePrefixDirtyControlConjugationData (Kind)
open ActivePrefixStageRuntimeData (Packed)

def SpecFor (a b c e : Kind) (m k r : ActivePrefixDirtyControlLoadProducer.Mode)
    {s : Shape} (input : ActivePrefixStageFullData.Inputs s) : Prop :=
  ∃ hp : 1 < input.stage.f → Packed input 1, ∀ x : Array s input.rows,
    HoareTime (ActivePrefixStageRuntimeProgram.programFor a b c e m k r)
      (fun w => w=ActivePrefixStageRuntimeProgram.bank input x)
      (fun w => w=ActivePrefixStageRuntimeProgram.bank input (ActivePrefixStageRuntimeData.result input x))
      (ActivePrefixStageRuntimeData.cost 1 input hp)

def Spec {s : Shape} (input : ActivePrefixStageFullData.Inputs s) : Prop :=
  SpecFor .tPure .tNegative .uPure .uNegative .pure .pure .pure input

theorem spec_for (a b c e : Kind) (m k r : ActivePrefixDirtyControlLoadProducer.Mode)
    {s : Shape} (input : ActivePrefixStageFullData.Inputs s)
    (hp : 1 < input.stage.f → Packed input 1)
    (h : ∀ x : Array s input.rows,
      HoareTime (ActivePrefixStageRuntimeProgram.programFor a b c e m k r)
        (fun w => w=ActivePrefixStageRuntimeProgram.bank input x)
        (fun w => w=ActivePrefixStageRuntimeProgram.bank input (ActivePrefixStageRuntimeData.result input x))
        (ActivePrefixStageRuntimeData.cost 1 input hp)) : SpecFor a b c e m k r input := ⟨hp,h⟩

theorem spec {s : Shape} (input : ActivePrefixStageFullData.Inputs s)
    (hp : 1 < input.stage.f → Packed input 1) : Spec input :=
  spec_for .tPure .tNegative .uPure .uNegative .pure .pure .pure input hp
    (fun x => ActivePrefixStageRuntimeRun.runs 1 input x hp)

/-- Density one and both repair records are proved from the actual choices. -/
theorem eventually_packed (c m : ℕ) (hc : 2≤c) (hm : 2≤m) :
    ∀ᶠ n : ℕ in Filter.atTop,
    ∀ (D payload j : ℕ) (_hcut : cutoff c m n≤D) (_hD : D≤d n)
      (_hpayload : 6*b n*2^ℓ n≤payload)
      (v : Stage (actualShape n c m D payload))
      (h : Ready (actualShape n c m D payload) v (rowsAt c m (d n) (K n) j)),
      Packed (inputs v (rowsAt c m (d n) (K n) j) h) 1 := by
  filter_upwards [CompactActualStageInputs.eventually_allowances c m hc hm] with n ha
  intro D payload j hcut hD hpayload v h
  have hE := ha D payload j hcut hD hpayload v h .early
  have hL := ha D payload j hcut hD hpayload v h .late
  have hb : 2≤(actualShape n c m D payload).guard := by
    change 2≤4*CompactScalarAllowances.guardLog n+6
    omega
  refine ⟨hb,h.repairGuard,hE.1,hL.1,?_,?_⟩
  · simpa only [Nat.cast_one,inputs,ActiveRepairLayoutRecordsHeadersData.repair,actualShape,CompactGlobalReservation.shape] using hE.2.1
  · simpa only [Nat.cast_one,inputs,ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair,actualShape,CompactGlobalReservation.shape] using hL.2.2

theorem eventually_runs (c m : ℕ) (hc : 2≤c) (hm : 2≤m) :
    ∀ᶠ n : ℕ in Filter.atTop,
    ∀ (D payload j : ℕ) (_hcut : cutoff c m n≤D) (_hD : D≤d n)
      (_hpayload : 6*b n*2^ℓ n≤payload)
      (v : Stage (actualShape n c m D payload))
      (h : Ready (actualShape n c m D payload) v (rowsAt c m (d n) (K n) j)),
      Spec (inputs v (rowsAt c m (d n) (K n) j) h) := by
  filter_upwards [eventually_packed c m hc hm] with n hp
  intro D payload j hcut hD hpayload v h
  exact spec _ (fun _ => hp D payload j hcut hD hpayload v h)

/-- Both geometry readiness and all packed allowances are synthesized; the
same machine executes singleton and packed stages in either source order. -/
theorem eventually_ready_runs (c m : ℕ) (hc : 2≤c) (hm : 2≤m) :
    ∀ᶠ n : ℕ in Filter.atTop,
    ∀ (D payload j : ℕ) (_hcut : cutoff c m n≤D) (_hD : D≤d n)
      (_hpayload : 6*b n*2^ℓ n≤payload) (_hj : j≤depth m (d n))
      (v : Stage (actualShape n c m D payload)),
      ∃ h : Ready (actualShape n c m D payload) v (rowsAt c m (d n) (K n) j),
        Spec (inputs v (rowsAt c m (d n) (K n) j) h) := by
  filter_upwards [CompactActualStageGeometry.eventually_ready c m hc hm,eventually_runs c m hc hm] with n hr hrun
  intro D payload j hcut hD hpayload hj v
  let h := hr D payload j hcut hD hpayload hj v
  exact ⟨h,hrun D payload j hcut hD hpayload v h⟩

end
end IntegerMultBounds.Machine.CompactActualStageRuntime
