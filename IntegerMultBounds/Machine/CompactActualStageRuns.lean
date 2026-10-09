import IntegerMultBounds.Machine.CompactActualStageInputs
import IntegerMultBounds.Machine.ActivePrefixStageFullBudget

/-! Actual original-slot stages execute with density constant one, with
repair width and density paid by multiplier choices and the global pad.
These are fixed original-input programs; runtime direction dispatch and
recursive iteration are separate. -/
namespace IntegerMultBounds.Machine.CompactActualStageRuns
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open CompactActualStageGeometry CompactActualStageAllowance CompactActualStageInputs
open CompactGlobalRowPadding CompactReservationCutoff
open Sizes
open ActiveRepairLayoutRecordsData (Array)

def EarlySpecFor (mode : ActivePrefixDirtyControlLoadProducer.Mode) {s : Shape} (input : ActivePrefixStageFullData.Inputs s)
    (horder : input.stage.source.val < input.stage.target.val) : Prop :=
  ∀ x : Array s input.rows, HoareTime (ActivePrefixStageFullEarlyRun.programFor mode)
    (fun w => w=ActivePrefixStageFullEarlyRun.bank input x)
    (fun w => w=ActivePrefixStageFullEarlyRun.bank input (ActivePrefixStageFullData.earlyResult input horder x))
    (ActivePrefixStageFullEarlyRun.cost 1 input horder)

def EarlySpec {s : Shape} (input : ActivePrefixStageFullData.Inputs s)
    (horder : input.stage.source.val < input.stage.target.val) := EarlySpecFor .pure input horder

def LateSpecFor (a b c e : ActivePrefixDirtyControlConjugationData.Kind)
    (mode : ActivePrefixDirtyControlLoadProducer.Mode) {s : Shape} (input : ActivePrefixStageFullData.Inputs s)
    (horder : input.stage.target.val < input.stage.source.val) : Prop :=
  ∃ (hn : 0 < input.stage.f-1) (hb : 2≤s.guard), ∀ x : Array s input.rows,
    HoareTime (ActivePrefixStageFullLateRun.programFor a b c e mode)
      (fun w => w=ActivePrefixStageFullLateRun.bank input x)
      (fun w => w=ActivePrefixStageFullLateRun.bank input (ActivePrefixStageFullData.lateResult input horder x))
      (ActivePrefixStageFullLateRun.cost 1 input horder hn hb)

def LateSpec {s : Shape} (input : ActivePrefixStageFullData.Inputs s)
    (horder : input.stage.target.val < input.stage.source.val) :=
  LateSpecFor .tPure .tNegative .uPure .uNegative .pure input horder

theorem early_spec_for (mode : ActivePrefixDirtyControlLoadProducer.Mode) {s : Shape}
    (input : ActivePrefixStageFullData.Inputs s) (horder : input.stage.source.val < input.stage.target.val)
    (h : ∀ x : Array s input.rows, HoareTime (ActiveRepairLayoutRecordsFullEarlyRun.programFor mode)
      (fun w => w=ActiveRepairLayoutRecordsFullEarlyRun.bank (ActivePrefixStageFullData.descriptors .early input) x)
      (fun w => w=ActiveRepairLayoutRecordsFullEarlyRun.bank (ActivePrefixStageFullData.descriptors .early input)
        (ActivePrefixStageFullData.earlyResult input horder x))
      (ActivePrefixStageFullEarlyRun.stageCost 1 input horder)) : EarlySpecFor mode input horder :=
  fun x => ActivePrefixStageFullEarlyRun.runs_for mode input x _ _ horder (h x)

theorem late_spec_for (a b c e : ActivePrefixDirtyControlConjugationData.Kind)
    (mode : ActivePrefixDirtyControlLoadProducer.Mode) {s : Shape} (input : ActivePrefixStageFullData.Inputs s)
    (horder : input.stage.target.val < input.stage.source.val) (hn : 0 < input.stage.f-1) (hb : 2≤s.guard)
    (h : ∀ x : Array s input.rows, HoareTime (ActiveRepairLayoutRecordsFullLateRun.programFor a b c e mode)
      (fun w => w=ActiveRepairLayoutRecordsFullLateRun.bank (ActivePrefixStageFullData.descriptors .late input) x)
      (fun w => w=ActiveRepairLayoutRecordsFullLateRun.bank (ActivePrefixStageFullData.descriptors .late input)
        (ActivePrefixStageFullData.lateResult input horder x))
      (ActivePrefixStageFullLateRun.stageCost 1 input horder hn hb)) : LateSpecFor a b c e mode input horder :=
  ⟨hn,hb,fun x => ActivePrefixStageFullLateRun.runs_for a b c e mode input x _ _ horder (h x)⟩

theorem early_spec {s : Shape} (input : ActivePrefixStageFullData.Inputs s)
    (horder : input.stage.source.val < input.stage.target.val) (hq3 : s.guard+3≤s.chunk)
    (hR : (ActiveRepairLayoutRecordsHeadersData.geom (ActivePrefixStageFullData.descriptors .early input)).addressBits+1≤s.payload)
    (hdensity : VaryingControlRepairDensity.earlyDensity s.chunk s.guard (input.stage.f-1)*
      ((ActiveRepairLayoutRecordsHeadersData.geom (ActivePrefixStageFullData.descriptors .early input)).addressBits+1)≤1) :
    EarlySpec input horder :=
  early_spec_for .pure input horder (fun x => ActiveRepairLayoutRecordsFullEarlyRun.runs
    (ActivePrefixStageFullData.descriptors .early input) x
    (ActivePrefixStageGeometry.early_fits input.stage horder) (ActivePrefixStageGeometry.early_high_positive input.stage horder)
    (positive_H input.stage input.hG) hq3 hR 1 (by simpa only [Nat.cast_one,parameters,ActiveRepairLayoutRecordsHeadersData.repair,
      ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair] using hdensity))

theorem late_spec {s : Shape} (input : ActivePrefixStageFullData.Inputs s)
    (horder : input.stage.target.val < input.stage.source.val) (hn : 0 < input.stage.f-1) (hb : 2≤s.guard)
    (hq3 : s.guard+3≤s.chunk)
    (hR : (ActiveRepairLayoutRecordsHeadersData.geom (ActivePrefixStageFullData.descriptors .late input)).addressBits+1≤s.payload)
    (hdensity : VaryingControlRepairDensity.lateDensity s.chunk s.guard (input.stage.f-1)*
      ((ActiveRepairLayoutRecordsHeadersData.geom (ActivePrefixStageFullData.descriptors .late input)).addressBits+1)≤1) :
    LateSpec input horder :=
  late_spec_for .tPure .tNegative .uPure .uNegative .pure input horder hn hb
    (fun x => ActiveRepairLayoutRecordsFullLateRun.runs (ActivePrefixStageFullData.descriptors .late input) x
      (ActivePrefixStageGeometry.late_fits input.stage horder) hn hb
      (positive_before input.stage) (positive_H input.stage input.hG) hq3 hR 1 (by simpa only [Nat.cast_one,parameters,ActiveRepairLayoutRecordsHeadersData.repair,
      ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair] using hdensity))

 theorem eventually_runs (c m : ℕ) (hc : 2≤c) (hm : 2≤m) :
    ∀ᶠ n : ℕ in Filter.atTop,
    ∀ (D payload j : ℕ) (_hcut : cutoff c m n≤D) (_hD : D≤d n)
      (_hpayload : 6*b n*2^ℓ n≤payload)
      (v : Stage (actualShape n c m D payload))
      (h : Ready (actualShape n c m D payload) v (rowsAt c m (d n) (K n) j)),
      let input := inputs v (rowsAt c m (d n) (K n) j) h
      (∀ horder : v.source.val<v.target.val, EarlySpec input horder) ∧
      (∀ (_hf : 2≤v.f) (horder : v.target.val<v.source.val), LateSpec input horder) := by
  filter_upwards [CompactActualStageInputs.eventually_allowances c m hc hm] with n ha
  intro D payload j hcut hD hpayload v h
  let input := inputs v (rowsAt c m (d n) (K n) j) h
  have hE := ha D payload j hcut hD hpayload v h .early
  have hL := ha D payload j hcut hD hpayload v h .late
  constructor
  · intro horder
    exact early_spec input horder h.repairGuard hE.1 hE.2.1
  · intro hf horder
    have hn : 0 < input.stage.f-1 := by change 0<v.f-1; omega
    have hb : 2≤(actualShape n c m D payload).guard := by
      change 2≤4*CompactScalarAllowances.guardLog n+6
      omega
    exact late_spec input horder hn hb h.repairGuard hL.1 hL.2.2

end
end IntegerMultBounds.Machine.CompactActualStageRuns
