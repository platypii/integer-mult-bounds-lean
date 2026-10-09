import IntegerMultBounds.Machine.CompactComplexPhasePhysicalBudget

/-! Actual scalar/cutoff/global-row choices compile each fixed complex edge
with a uniform certified machine bound and exact original-address controls. -/
namespace IntegerMultBounds.Machine.CompactActualComplexPhase
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open CompactActualStageGeometry CompactActualStageAllowance CompactActualStageInputs
open CompactGlobalRowPadding CompactReservationCutoff Sizes
open ActiveRepairLayoutRecordsData (Array)
open Networks.ComplexPhaseRowSchedule (Edge dimension slot)
open CompactComplexPhasePhysical (word destination originalCoordinates control)
variable {s : Shape}

def Spec (C : ℝ) (input : ActivePrefixStageFullData.Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge) : Prop :=
  CompactComplexPhasePhysicalBudget.BoundedSpec C input hslots edge ∧
  (∀ x : Array s input.rows, ∀ k : Fin (input.rows*s.recordWidth),
    ActivePrefixStagePairSchedule.result input (word input hslots edge) x (destination input hslots edge k)=x k) ∧
  (∀ (k : Fin (input.rows*s.recordWidth)) (axis : Fin input.stage.f) (i : Fin (dimension edge)),
    control input hslots edge k axis i=Networks.BinaryRowProgram.run
      (Networks.ComplexPhaseRowSchedule.word edge) (originalCoordinates input hslots k axis) (slot edge i))

theorem spec (C : ℝ) (input : ActivePrefixStageFullData.Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (h : CompactComplexPhasePhysicalBudget.BoundedSpec C input hslots edge) : Spec C input hslots edge :=
  ⟨h,CompactComplexPhasePhysical.entry input hslots edge,CompactComplexPhasePhysical.computed_control input hslots edge⟩

theorem eventually_bounded (c m : ℕ) (hc : 2≤c) (hm : 2≤m) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in Filter.atTop,
    ∀ (D payload j : ℕ) (_hcut : cutoff c m n≤D) (_hD : D≤d n)
      (_hpayload : 6*b n*2^ℓ n≤payload) (_hj : j≤depth m (d n))
      (v : Stage (actualShape n c m D payload)) (hslots : v.slots=25^3) (edge : Edge),
      ∃ h : Ready (actualShape n c m D payload) v (rowsAt c m (d n) (K n) j),
        Spec C (inputs v (rowsAt c m (d n) (K n) j) h) hslots edge := by
  obtain ⟨C,hC,hbound⟩ := CompactComplexPhasePhysicalBudget.uniform_bound
  refine ⟨C,hC,?_⟩
  filter_upwards [CompactActualStageGeometry.eventually_ready c m hc hm,
    CompactActualPairSchedule.eventually_runs c m hc hm] with n hr hrun
  intro D payload j hcut hD hpayload hj v hslots edge
  let h := hr D payload j hcut hD hpayload hj v
  let input := inputs v (rowsAt c m (d n) (K n) j) h
  have hs := hrun D payload j hcut hD hpayload v h (word input hslots edge)
  exact ⟨h,spec C input hslots edge (hbound _ input hslots edge hs)⟩

end
end IntegerMultBounds.Machine.CompactActualComplexPhase
