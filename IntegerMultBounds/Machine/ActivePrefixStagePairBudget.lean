import IntegerMultBounds.Machine.ActivePrefixStagePairSchedule
import IntegerMultBounds.Machine.ActivePrefixStageRuntimeBudget
import IntegerMultBounds.Machine.ActivePrefixStageInverseBudget

/-! Saving the original pair, writing each literal instruction, restoring the
pair and all joins are charged. A fixed finite word retains the stage exponent;
its only extra factor is its fixed number of row additions. -/
namespace IntegerMultBounds.Machine.ActivePrefixStagePairBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStagePairData (changePair pairWords focus)
open RecursiveChildQuotientsConstant (bits)
open Networks.BinaryRowProgram (Op)
open ActivePrefixStageInverseBudget (scale)
variable {s : Shape}

def volume (d : Inputs s) : ℕ := d.rows*s.recordWidth

theorem volume_positive (d : Inputs s) : 0<volume d := by
  have hp : 0<s.payload := by have := d.hrecord; omega
  have hr := d.hr
  unfold volume Shape.recordWidth
  positivity

theorem slots_bound (d : Inputs s) : d.stage.slots≤volume d := by
  rcases ActivePrefixStageGeometry.source_order d.stage with h | h
  · exact (ActivePrefixStageHeadersBudget.original_bounds .early d.stage d.rows d.hG d.hGK h d.hr d.hrecord).1 6
  · exact (ActivePrefixStageHeadersBudget.original_bounds .late d.stage d.rows d.hG d.hGK h d.hr d.hrecord).1 6

theorem slot_bits_bound (d : Inputs s) (i : Fin d.stage.slots) : (bits i.val).length≤volume d+1 := by
  have h := GrowingCounterData.canonical_width (bits i.val) (RecursiveChildQuotientsConstant.bits_canonical _)
  rw [RecursiveChildQuotientsConstant.bits_value] at h
  have hl := Nat.log2_le_self i.val
  have hs := slots_bound d
  have hi := i.isLt
  omega

theorem pair_words_bound (d : Inputs s) (i : Fin 2) : (pairWords d i).length≤volume d+1 := by
  fin_cases i
  · exact slot_bits_bound d d.stage.source
  · exact slot_bits_bound d d.stage.target

theorem rewrite_bound (d : Inputs s) (op : Op (Fin d.stage.slots)) :
    ActivePrefixStagePairData.cost d op≤43*volume d := by
  have hs := slots_bound d
  have h := ActivePrefixStageSlotRewrite.pair_cost_bound
    (bits d.stage.source.val) (bits d.stage.target.val) op.source.val op.target.val (volume d)
    (RecursiveChildQuotientsConstant.bits_canonical _) (RecursiveChildQuotientsConstant.bits_canonical _)
    (by rw [RecursiveChildQuotientsConstant.bits_value]; have := d.stage.source.isLt; omega)
    (by rw [RecursiveChildQuotientsConstant.bits_value]; have := d.stage.target.isLt; omega)
    (by have := op.source.isLt; omega) (by have := op.target.isLt; omega)
  have hv := volume_positive d
  exact h.trans (by omega)

theorem overhead_bound (d : Inputs s) (op : Op (Fin d.stage.slots)) (B : ℕ) :
    ActivePrefixStagePairRun.cost d op B≤B+113*volume d := by
  have h := BinaryPairFrame.cost_bound focus ActivePrefixStagePairData.focus_injective
    (pairWords d) (pairWords (changePair d op)) (ActivePrefixStagePairData.cost d op+B+1)
    (volume d) (volume_positive d) (pair_words_bound d)
    (fun i => pair_words_bound (changePair d op) i)
  have hr := rewrite_bound d op
  have hv := volume_positive d
  exact h.trans (by omega)

theorem volume_le_scale (d : Inputs s) : (volume d : ℝ)≤scale d := by
  have he : (1 : ℝ)≤((max 1 ((d.stage.f-1)*s.guard) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau :=
    Real.one_le_rpow (by exact_mod_cast le_max_left 1 ((d.stage.f-1)*s.guard))
      Shared50RecursiveBudgetBound.exponent_range.1.le
  exact le_mul_of_one_le_right (by positivity) he

theorem pair_uniform_bound (D : ℕ) : ∃ C : ℝ,0<C ∧
    ∀ (s : Shape) (d : Inputs s) (op : Op (Fin d.stage.slots))
      (hp : 1<d.stage.f → ActivePrefixStageRuntimeData.Packed (changePair d op) D),
      (ActivePrefixStagePairRun.cost d op
        (ActivePrefixStageRuntimeData.cost D (changePair d op) hp) : ℝ)≤C*scale d := by
  obtain ⟨C,hC,h⟩ := ActivePrefixStageRuntimeBudget.uniform_bound D
  refine ⟨C+113,by positivity,?_⟩
  intro s d op hp
  have hb := h s (changePair d op) hp
  have ho := overhead_bound d op (ActivePrefixStageRuntimeData.cost D (changePair d op) hp)
  have hv := volume_le_scale d
  have hb' : (ActivePrefixStageRuntimeData.cost D (changePair d op) hp : ℝ)≤C*scale d := by
    simpa only [scale,changePair,mul_assoc] using hb
  have ho' : (ActivePrefixStagePairRun.cost d op
      (ActivePrefixStageRuntimeData.cost D (changePair d op) hp) : ℝ)≤
      (ActivePrefixStageRuntimeData.cost D (changePair d op) hp : ℝ)+113*(volume d : ℝ) := by exact_mod_cast ho
  nlinarith only [hb',ho',hv]

theorem sum_bound (d : Inputs s) (B : Op (Fin d.stage.slots) → ℕ) (C : ℝ)
    (h : ∀ op,(B op : ℝ)≤C*scale d) (ops : List (Op (Fin d.stage.slots))) :
    (ActivePrefixStagePairSchedule.cost B ops : ℝ)≤(ops.length : ℝ)*(C+1)*scale d := by
  induction ops with
  | nil => simp [ActivePrefixStagePairSchedule.cost]
  | cons op ops ih =>
    have hb := h op
    have hu := ActivePrefixStageInverseBudget.one_le_scale d
    change ((B op+1+ActivePrefixStagePairSchedule.cost B ops : ℕ) : ℝ)≤
      ((ops.length+1 : ℕ) : ℝ)*(C+1)*scale d
    push_cast
    nlinarith only [hb,hu,ih]

/-- Fixed word length changes only the constant; no runtime column count
or word-descriptor scan adds another width exponent. -/
theorem schedule_uniform_bound (D : ℕ) : ∃ C : ℝ,0<C ∧
    ∀ (s : Shape) (d : Inputs s)
      (hp : ∀ op,1<d.stage.f → ActivePrefixStageRuntimeData.Packed (changePair d op) D)
      (ops : List (Op (Fin d.stage.slots))),
      (ActivePrefixStagePairSchedule.cost (ActivePrefixStagePairSchedule.stageCost D d hp) ops : ℝ)≤
        (ops.length : ℝ)*C*scale d := by
  obtain ⟨C,hC,h⟩ := pair_uniform_bound D
  refine ⟨C+1,by positivity,?_⟩
  intro s d hp ops
  exact sum_bound d _ C (fun op => h s d op (hp op)) ops

end
end IntegerMultBounds.Machine.ActivePrefixStagePairBudget
