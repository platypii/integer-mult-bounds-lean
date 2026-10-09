import IntegerMultBounds.Machine.CompactComplexPhasePhysical
import IntegerMultBounds.Machine.CompactActualPairScheduleBudget

/-! One fixed complex-network compiler constant pays all literal row stages,
including backup, rewritten pair words, flag cleanup and restored tapes. -/
namespace IntegerMultBounds.Machine.CompactComplexPhasePhysicalBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixDirtyControlConjugationData (Kind)
open ActiveRepairLayoutRecordsData (Array)
open Networks.BinaryRowProgram (Op)
open Networks.ComplexPhaseRowSchedule (Edge)
open CompactComplexPhasePhysical (word)
open ActivePrefixStageInverseBudget (scale)
open ActivePrefixStageRuntimeData (Packed)
open ActivePrefixStagePairData (changePair)
variable {s : Shape}

def instructionCount : ℕ :=
  (Networks.ComplexPhaseBudget.edges.attach.map (fun edge => (Networks.ComplexPhaseRowSchedule.word edge).length)).sum

theorem word_length (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge) :
    (word input hslots edge).length=(Networks.ComplexPhaseRowSchedule.word edge).length := by
  simp [word,CompactComplexPhaseSchedule.nodeWord]

theorem word_bound (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge) :
    (word input hslots edge).length≤ instructionCount := by
  rw [word_length]
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨edge,List.mem_attach _ edge,rfl⟩)

def BoundedSpecFor (a b c e : Kind) (m k r : ActivePrefixDirtyControlLoadProducer.Mode)
    (C : ℝ) (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge) : Prop :=
  ∃ hp : ∀ op,1 < input.stage.f → Packed (changePair input op) 1,
    (ActivePrefixStagePairSchedule.cost (ActivePrefixStagePairSchedule.stageCost 1 input hp) (word input hslots edge) : ℝ)≤C*scale input ∧
    ∀ x : Array s input.rows,
      HoareTime (ActivePrefixStagePairSchedule.programFor a b c e m k r (word input hslots edge))
        (fun w => w=ActivePrefixStagePairRun.bank input x)
        (fun w => w=ActivePrefixStagePairRun.bank input (ActivePrefixStagePairSchedule.result input (word input hslots edge) x))
        (ActivePrefixStagePairSchedule.cost (ActivePrefixStagePairSchedule.stageCost 1 input hp) (word input hslots edge))

def BoundedSpec := BoundedSpecFor (s := s) .tPure .tNegative .uPure .uNegative .pure .pure .pure

theorem bounded_for (a b c e : Kind) (m k r : ActivePrefixDirtyControlLoadProducer.Mode)
    (C : ℝ) (hC : 0≤C) (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (h : CompactActualPairScheduleBudget.BoundedSpecFor a b c e m k r C input (word input hslots edge)) :
    BoundedSpecFor a b c e m k r ((instructionCount+1)*C) input hslots edge := by
  obtain ⟨hp,hb,hrun⟩ := h
  refine ⟨hp,hb.trans ?_,hrun⟩
  have hl : ((word input hslots edge).length : ℝ)≤(instructionCount+1 : ℝ) := by
    exact_mod_cast (word_bound input hslots edge).trans (Nat.le_add_right _ _)
  have hmul := mul_le_mul_of_nonneg_right hl (show 0≤C*scale input by
    have hs := ActivePrefixStageInverseBudget.one_le_scale input
    positivity)
  simpa only [mul_assoc] using hmul

/-- The constant is uniform over every actual ordered complex25 edge and
all runtime widths, selected columns and original reservation sizes. -/
theorem uniform_bound : ∃ C : ℝ,0<C ∧
    ∀ (s : Shape) (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge),
      CompactActualPairSchedule.Spec input (word input hslots edge) → BoundedSpec C input hslots edge := by
  obtain ⟨C,hC,hb⟩ := CompactActualPairScheduleBudget.uniform_bound
  refine ⟨(instructionCount+1)*C,by positivity,?_⟩
  intro s input hslots edge h
  exact bounded_for .tPure .tNegative .uPure .uNegative .pure .pure .pure C hC.le input hslots edge
    (hb s input (word input hslots edge) h)

end
end IntegerMultBounds.Machine.CompactComplexPhasePhysicalBudget
