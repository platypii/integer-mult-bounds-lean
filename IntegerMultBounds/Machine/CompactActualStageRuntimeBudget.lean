import IntegerMultBounds.Machine.CompactActualStageRuntime

/-! One uniform constant bounds the actual all-width stage on every global
row level, with density fixed at one and the certified compact exponent. -/
namespace IntegerMultBounds.Machine.CompactActualStageRuntimeBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open CompactActualStageGeometry CompactActualStageAllowance CompactActualStageInputs
open CompactActualStageRuntime
open CompactGlobalRowPadding CompactReservationCutoff
open Sizes
open ActiveRepairLayoutRecordsData (Array)
open ActivePrefixDirtyControlConjugationData (Kind)
open ActivePrefixStageRuntimeData (Packed)

def BoundedSpecFor (a b c e : Kind) (m k r : ActivePrefixDirtyControlLoadProducer.Mode)
    (C : ℝ) {s : Shape} (input : ActivePrefixStageFullData.Inputs s) : Prop :=
  ∃ hp : 1 < input.stage.f → Packed input 1,
    (ActivePrefixStageRuntimeData.cost 1 input hp : ℝ)≤C*(input.rows*s.recordWidth : ℕ)*
      ((max 1 ((input.stage.f-1)*s.guard) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau ∧
    ∀ x : Array s input.rows,
      HoareTime (ActivePrefixStageRuntimeProgram.programFor a b c e m k r)
        (fun w => w=ActivePrefixStageRuntimeProgram.bank input x)
        (fun w => w=ActivePrefixStageRuntimeProgram.bank input (ActivePrefixStageRuntimeData.result input x))
        (ActivePrefixStageRuntimeData.cost 1 input hp)

def BoundedSpec (C : ℝ) {s : Shape} (input : ActivePrefixStageFullData.Inputs s) : Prop :=
  BoundedSpecFor .tPure .tNegative .uPure .uNegative .pure .pure .pure C input

theorem bounded_for (a b c e : Kind) (m k r : ActivePrefixDirtyControlLoadProducer.Mode)
    (C : ℝ) {s : Shape} (input : ActivePrefixStageFullData.Inputs s)
    (h : SpecFor a b c e m k r input)
    (hb : ∀ hp : 1 < input.stage.f → Packed input 1,
      (ActivePrefixStageRuntimeData.cost 1 input hp : ℝ)≤C*(input.rows*s.recordWidth : ℕ)*
        ((max 1 ((input.stage.f-1)*s.guard) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau) :
    BoundedSpecFor a b c e m k r C input := by
  obtain ⟨hp,hrun⟩ := h
  exact ⟨hp,hb hp,hrun⟩

theorem uniform_bound : ∃ C : ℝ,0<C ∧
    ∀ (s : Shape) (input : ActivePrefixStageFullData.Inputs s), Spec input → BoundedSpec C input := by
  obtain ⟨C,hC,hb⟩ := ActivePrefixStageRuntimeBudget.uniform_bound 1
  refine ⟨C,hC,?_⟩
  intro s input h
  exact bounded_for .tPure .tNegative .uPure .uNegative .pure .pure .pure C input h (hb s input)

/-- The actual stage has a uniform certified bound with no caller-supplied
allowance, readiness, width case or source direction. -/
theorem eventually_bounded (c m : ℕ) (hc : 2≤c) (hm : 2≤m) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in Filter.atTop,
    ∀ (D payload j : ℕ) (_hcut : cutoff c m n≤D) (_hD : D≤d n)
      (_hpayload : 6*b n*2^ℓ n≤payload) (_hj : j≤depth m (d n))
      (v : Stage (actualShape n c m D payload)),
      ∃ h : Ready (actualShape n c m D payload) v (rowsAt c m (d n) (K n) j),
        BoundedSpec C (inputs v (rowsAt c m (d n) (K n) j) h) := by
  obtain ⟨C,hC,hbound⟩ := uniform_bound
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ready_runs c m hc hm] with n hn
  intro D payload j hcut hD hpayload hj v
  obtain ⟨h,hrun⟩ := hn D payload j hcut hD hpayload hj v
  exact ⟨h,hbound _ _ hrun⟩

end
end IntegerMultBounds.Machine.CompactActualStageRuntimeBudget
