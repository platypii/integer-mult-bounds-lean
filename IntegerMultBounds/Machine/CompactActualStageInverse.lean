import IntegerMultBounds.Machine.CompactActualStageDispatch
import IntegerMultBounds.Machine.ActivePrefixStageInverseBudget

/-! Actual density-one original-input stages implement recursive return and
round trips without additional geometry or allowance assumptions. -/
namespace IntegerMultBounds.Machine.CompactActualStageInverse
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixDirtyControlConjugationData (Kind)
open ActivePrefixStageParameters
open CompactActualStageGeometry CompactActualStageAllowance CompactActualStageInputs
open CompactGlobalRowPadding CompactReservationCutoff Sizes
variable {s : Shape}

theorem early_for (mode : ActivePrefixDirtyControlLoadProducer.Mode) (input : Inputs s)
    (ho : input.stage.source.val< input.stage.target.val)
    (h : CompactActualStageRuns.EarlySpecFor mode input ho) :
    ActivePrefixStageFullInverseRun.Early.UndoSpecFor mode 1 input ho ∧
    ActivePrefixStageFullInverseRun.Early.PairSpecFor mode 1 input ho :=
  ⟨ActivePrefixStageFullInverseRun.Early.undo_spec_for mode 1 input ho h,
   ActivePrefixStageFullInverseRun.Early.pair_spec_for mode 1 input ho h⟩

theorem late_for (a b c e : Kind) (mode : ActivePrefixDirtyControlLoadProducer.Mode)
    (input : Inputs s) (ho : input.stage.target.val< input.stage.source.val)
    (h : CompactActualStageRuns.LateSpecFor a b c e mode input ho) :
    ∃ (hn : 0< input.stage.f-1) (hb : 2≤s.guard),
      ActivePrefixStageFullInverseRun.Late.UndoSpecFor a b c e mode 1 input ho hn hb ∧
      ActivePrefixStageFullInverseRun.Late.PairSpecFor a b c e mode 1 input ho hn hb := by
  obtain ⟨hn,hb,hh⟩ := h
  exact ⟨hn,hb,ActivePrefixStageFullInverseRun.Late.undo_spec_for a b c e mode 1 input ho hn hb hh,
    ActivePrefixStageFullInverseRun.Late.pair_spec_for a b c e mode 1 input ho hn hb hh⟩

def SpecFor (a b c e : Kind) (m k : ActivePrefixDirtyControlLoadProducer.Mode) (input : Inputs s) : Prop :=
  ∃ (hn : 0< input.stage.f-1) (hb : 2≤s.guard),
    ActivePrefixStageDispatchInverseRun.UndoSpecFor a b c e m k 1 input hn hb ∧
    ActivePrefixStageDispatchInverseRun.PairSpecFor a b c e m k 1 input hn hb

def Spec := SpecFor (s := s) .tPure .tNegative .uPure .uNegative .pure .pure

theorem spec_for (a b c e : Kind) (m k : ActivePrefixDirtyControlLoadProducer.Mode)
    (input : Inputs s) (h : CompactActualStageDispatch.SpecFor a b c e m k input) :
    SpecFor a b c e m k input := by
  obtain ⟨hn,hb,hh⟩ := h
  exact ⟨hn,hb,ActivePrefixStageDispatchInverseRun.undo_spec_for a b c e m k 1 input hn hb hh,
    ActivePrefixStageDispatchInverseRun.pair_spec_for a b c e m k 1 input hn hb hh⟩

theorem spec (input : Inputs s) (h : CompactActualStageDispatch.Spec input) : Spec input :=
  spec_for .tPure .tNegative .uPure .uNegative .pure .pure input h

theorem eventually_ready_runs (c m : ℕ) (hc : 2≤c) (hm : 2≤m) :
    ∀ᶠ n : ℕ in Filter.atTop,
    ∀ (D payload j : ℕ) (_hcut : cutoff c m n≤D) (_hD : D≤d n)
      (_hpayload : 6*b n*2^ℓ n≤payload) (_hj : j≤depth m (d n))
      (v : Stage (actualShape n c m D payload)) (_hf : 2≤v.f),
      ∃ h : Ready (actualShape n c m D payload) v (rowsAt c m (d n) (K n) j),
        Spec (inputs v (rowsAt c m (d n) (K n) j) h) := by
  filter_upwards [CompactActualStageDispatch.eventually_ready_runs c m hc hm] with n hr
  intro D payload j hcut hD hpayload hj v hf
  obtain ⟨h,hs⟩ := hr D payload j hcut hD hpayload hj v hf
  exact ⟨h,spec _ hs⟩

end
end IntegerMultBounds.Machine.CompactActualStageInverse
