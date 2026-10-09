import IntegerMultBounds.Machine.CompactActualStageRuns
import IntegerMultBounds.Machine.ActivePrefixStageDispatchSelected

/-! The fixed original-input runtime direction dispatcher executes actual
multiplier stages at density constant one. Scalar choices, cutoff and global
rows supply every repair allowance; no node direction or width is an input. -/
namespace IntegerMultBounds.Machine.CompactActualStageDispatch
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open CompactActualStageGeometry CompactActualStageAllowance CompactActualStageInputs
open CompactGlobalRowPadding CompactReservationCutoff
open Sizes
open ActiveRepairLayoutRecordsData (Array)
open ActivePrefixDirtyControlConjugationData (Kind)

def SpecFor (a b c e : Kind) (m k : ActivePrefixDirtyControlLoadProducer.Mode)
    {s : Shape} (input : ActivePrefixStageFullData.Inputs s) : Prop :=
  ∃ (hn : 0 < input.stage.f-1) (hb : 2≤s.guard), ∀ x : Array s input.rows,
    HoareTime (ActivePrefixStageDispatchRun.programFor a b c e m k)
      (fun w => w=ActivePrefixStageDispatchRun.bank input x)
      (fun w => w=ActivePrefixStageDispatchRun.bank input (ActivePrefixStageDispatchData.result input x))
      (ActivePrefixStageDispatchRun.cost 1 input hn hb)

def Spec {s : Shape} (input : ActivePrefixStageFullData.Inputs s) :=
  SpecFor .tPure .tNegative .uPure .uNegative .pure .pure input

theorem spec_for (a b c e : Kind) (m k : ActivePrefixDirtyControlLoadProducer.Mode)
    {s : Shape} (input : ActivePrefixStageFullData.Inputs s)
    (hn : 0 < input.stage.f-1) (hb : 2≤s.guard)
    (hE : ∀ ho : input.stage.source.val < input.stage.target.val,CompactActualStageRuns.EarlySpecFor k input ho)
    (hL : ∀ ho : input.stage.target.val < input.stage.source.val,CompactActualStageRuns.LateSpecFor a b c e m input ho) :
    SpecFor a b c e m k input := by
  refine ⟨hn,hb,?_⟩
  intro x
  by_cases h : input.stage.source.val < input.stage.target.val
  · have hr : ActivePrefixStageDispatchData.result input x=ActivePrefixStageFullData.earlyResult input h x := dite_eq_left h
    have hc : ActivePrefixStageDispatchRun.cost 1 input hn hb=ActivePrefixStageOrderCompare.cost input.stage+
        ActivePrefixStageFullEarlyRun.cost 1 input h+4 := dite_eq_left h
    have hh := ActivePrefixStageDispatchRun.early_dispatch a b c e m k input x _ _ h (hE h x)
    exact hh.consequence (fun _ hv => hv)
      (fun _ hv => hv.trans (congrArg (ActivePrefixStageDispatchRun.bank input) hr.symm)) hc.symm.le
  · have ho := ActivePrefixStageOrderCompare.late_of_not_early input.stage h
    obtain ⟨hn',hb',hl⟩ := hL ho
    have hr : ActivePrefixStageDispatchData.result input x=ActivePrefixStageFullData.lateResult input ho x := dite_eq_right h
    have hc : ActivePrefixStageDispatchRun.cost 1 input hn hb=ActivePrefixStageOrderCompare.cost input.stage+
        ActivePrefixStageFullLateRun.cost 1 input ho hn' hb'+4 := dite_eq_right h
    have hh := ActivePrefixStageDispatchRun.late_dispatch a b c e m k input x _ _ ho (hl x)
    exact hh.consequence (fun _ hv => hv)
      (fun _ hv => hv.trans (congrArg (ActivePrefixStageDispatchRun.bank input) hr.symm)) hc.symm.le

theorem spec {s : Shape} (input : ActivePrefixStageFullData.Inputs s)
    (hn : 0 < input.stage.f-1) (hb : 2≤s.guard) (hq3 : s.guard+3≤s.chunk)
    (hRE : (ActiveRepairLayoutRecordsHeadersData.geom (ActivePrefixStageFullData.descriptors .early input)).addressBits+1≤s.payload)
    (hRL : (ActiveRepairLayoutRecordsHeadersData.geom (ActivePrefixStageFullData.descriptors .late input)).addressBits+1≤s.payload)
    (hDE : VaryingControlRepairDensity.earlyDensity s.chunk s.guard (input.stage.f-1)*
      ((ActiveRepairLayoutRecordsHeadersData.geom (ActivePrefixStageFullData.descriptors .early input)).addressBits+1)≤1)
    (hDL : VaryingControlRepairDensity.lateDensity s.chunk s.guard (input.stage.f-1)*
      ((ActiveRepairLayoutRecordsHeadersData.geom (ActivePrefixStageFullData.descriptors .late input)).addressBits+1)≤1) :
    Spec input :=
  spec_for .tPure .tNegative .uPure .uNegative .pure .pure input hn hb
    (fun ho => CompactActualStageRuns.early_spec input ho hq3 hRE hDE)
    (fun ho => CompactActualStageRuns.late_spec input ho hn hb hq3 hRL hDL)

theorem eventually_runs (c m : ℕ) (hc : 2≤c) (hm : 2≤m) :
    ∀ᶠ n : ℕ in Filter.atTop,
    ∀ (D payload j : ℕ) (_hcut : cutoff c m n≤D) (_hD : D≤d n)
      (_hpayload : 6*b n*2^ℓ n≤payload)
      (v : Stage (actualShape n c m D payload)) (_hf : 2≤v.f)
      (h : Ready (actualShape n c m D payload) v (rowsAt c m (d n) (K n) j)),
      Spec (inputs v (rowsAt c m (d n) (K n) j) h) := by
  filter_upwards [CompactActualStageInputs.eventually_allowances c m hc hm] with n ha
  intro D payload j hcut hD hpayload v hf h
  let input := inputs v (rowsAt c m (d n) (K n) j) h
  have hE := ha D payload j hcut hD hpayload v h .early
  have hL := ha D payload j hcut hD hpayload v h .late
  have hn : 0 < input.stage.f-1 := by change 0 < v.f-1; omega
  have hb : 2≤(actualShape n c m D payload).guard := by
    change 2≤4*CompactScalarAllowances.guardLog n+6
    omega
  exact spec input hn hb h.repairGuard hE.1 hL.1 hE.2.1 hL.2.2

/-- Geometry readiness is also synthesized by actual scalar and row choices. -/
theorem eventually_ready_runs (c m : ℕ) (hc : 2≤c) (hm : 2≤m) :
    ∀ᶠ n : ℕ in Filter.atTop,
    ∀ (D payload j : ℕ) (_hcut : cutoff c m n≤D) (_hD : D≤d n)
      (_hpayload : 6*b n*2^ℓ n≤payload) (_hj : j≤depth m (d n))
      (v : Stage (actualShape n c m D payload)) (_hf : 2≤v.f),
      ∃ h : Ready (actualShape n c m D payload) v (rowsAt c m (d n) (K n) j),
        Spec (inputs v (rowsAt c m (d n) (K n) j) h) := by
  filter_upwards [CompactActualStageGeometry.eventually_ready c m hc hm,eventually_runs c m hc hm] with n hr hrun
  intro D payload j hcut hD hpayload hj v hf
  let h := hr D payload j hcut hD hpayload hj v
  exact ⟨h,hrun D payload j hcut hD hpayload v hf h⟩

end
end IntegerMultBounds.Machine.CompactActualStageDispatch
