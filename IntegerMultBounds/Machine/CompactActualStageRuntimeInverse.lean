import IntegerMultBounds.Machine.CompactActualStageRuntime
import IntegerMultBounds.Machine.ActivePrefixStageRuntimeInverseBudget

/-! Actual choices provide a physical reverse and round trip for every
positive runtime width, with complete caller/private-bank restoration. -/
namespace IntegerMultBounds.Machine.CompactActualStageRuntimeInverse
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixDirtyControlConjugationData (Kind)
open ActivePrefixStageParameters
open CompactActualStageGeometry CompactActualStageAllowance CompactActualStageInputs
open CompactGlobalRowPadding CompactReservationCutoff Sizes
open ActivePrefixStageRuntimeData (Packed)
variable {s : Shape}

def SpecFor (a b c e : Kind) (m k r : ActivePrefixDirtyControlLoadProducer.Mode) (input : Inputs s) : Prop :=
  ∃ hp : 1< input.stage.f → Packed input 1,
    ActivePrefixStageRuntimeInverseRun.UndoSpecFor a b c e m k r 1 input hp ∧
    ActivePrefixStageRuntimeInverseRun.PairSpecFor a b c e m k r 1 input hp

def Spec := SpecFor (s := s) .tPure .tNegative .uPure .uNegative .pure .pure .pure

theorem spec_for (a b c e : Kind) (m k r : ActivePrefixDirtyControlLoadProducer.Mode)
    (input : Inputs s) (h : CompactActualStageRuntime.SpecFor a b c e m k r input) :
    SpecFor a b c e m k r input := by
  obtain ⟨hp,hh⟩ := h
  exact ⟨hp,ActivePrefixStageRuntimeInverseRun.undo_spec_for a b c e m k r 1 input hp hh,
    ActivePrefixStageRuntimeInverseRun.pair_spec_for a b c e m k r 1 input hp hh⟩

theorem spec (input : Inputs s) (h : CompactActualStageRuntime.Spec input) : Spec input :=
  spec_for .tPure .tNegative .uPure .uNegative .pure .pure .pure input h

theorem eventually_ready_runs (c m : ℕ) (hc : 2≤c) (hm : 2≤m) :
    ∀ᶠ n : ℕ in Filter.atTop,
    ∀ (D payload j : ℕ) (_hcut : cutoff c m n≤D) (_hD : D≤d n)
      (_hpayload : 6*b n*2^ℓ n≤payload) (_hj : j≤depth m (d n))
      (v : Stage (actualShape n c m D payload)),
      ∃ h : Ready (actualShape n c m D payload) v (rowsAt c m (d n) (K n) j),
        Spec (inputs v (rowsAt c m (d n) (K n) j) h) := by
  filter_upwards [CompactActualStageRuntime.eventually_ready_runs c m hc hm] with n hr
  intro D payload j hcut hD hpayload hj v
  obtain ⟨h,hs⟩ := hr D payload j hcut hD hpayload hj v
  exact ⟨h,spec _ hs⟩

end
end IntegerMultBounds.Machine.CompactActualStageRuntimeInverse
