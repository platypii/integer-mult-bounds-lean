import IntegerMultBounds.Machine.ActivePrefixStageNativePairSchedule
import IntegerMultBounds.Machine.ActivePrefixStagePairBudget

/-! Complete native basis words retain the certified stage exponent. Every
header frame, physical rewrite, conversion, restoration and join is charged;
the sole schedule factor is its fixed literal instruction count. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageNativePairBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStagePairData (changePair pairWords)
open ActivePrefixStageNativePairData (focus focus_injective)
open ActivePrefixStagePairBudget (volume volume_positive pair_words_bound rewrite_bound volume_le_scale)
open ActivePrefixStageInverseBudget (scale)
open Networks.BinaryRowProgram (Op)
variable {s : Shape}

theorem overhead_bound (d : Inputs s) (op : Op (Fin d.stage.slots)) (stageCost : ℕ) :
    ActivePrefixStageNativePairRun.cost d op stageCost≤stageCost+113*volume d := by
  have h := BinaryPairFrame.cost_bound focus focus_injective
    (pairWords d) (pairWords (changePair d op)) (ActivePrefixStageNativePairData.cost d op+stageCost+1)
    (volume d) (volume_positive d) (pair_words_bound d)
    (fun i => pair_words_bound (changePair d op) i)
  have hr := rewrite_bound d op
  change ActivePrefixStageNativePairData.cost d op≤43*volume d at hr
  have hv := volume_positive d
  exact h.trans (by omega)

theorem pair_uniform_bound (D : ℕ) : ∃ C : ℝ,0<C ∧
    ∀ (s : Shape) (B : ℕ) (d : Inputs s) (_hcode : s.payload=B*3+0)
      (op : Op (Fin d.stage.slots))
      (hp : 1<d.stage.f → ActivePrefixStageRuntimeData.Packed (changePair d op) D),
      (ActivePrefixStageNativePairRun.cost d op
        (ActivePrefixStageNative.cost (B:=B) D (changePair d op) hp) : ℝ)≤C*scale d := by
  obtain ⟨C,hC,h⟩ := ActivePrefixStageNative.uniform_bound D
  refine ⟨C+113,by positivity,?_⟩
  intro s B d hcode op hp
  have hb := h s B (changePair d op) hcode hp
  have ho := overhead_bound d op (ActivePrefixStageNative.cost (B:=B) D (changePair d op) hp)
  have hv := volume_le_scale d
  have hb' : (ActivePrefixStageNative.cost (B:=B) D (changePair d op) hp : ℝ)≤C*scale d := by
    simpa only [scale,changePair,mul_assoc] using hb
  have ho' : (ActivePrefixStageNativePairRun.cost d op
      (ActivePrefixStageNative.cost (B:=B) D (changePair d op) hp) : ℝ)≤
      (ActivePrefixStageNative.cost (B:=B) D (changePair d op) hp : ℝ)+113*(volume d : ℝ) := by
    exact_mod_cast ho
  nlinarith only [hb',ho',hv]

theorem schedule_uniform_bound (D : ℕ) : ∃ C : ℝ,0<C ∧
    ∀ (s : Shape) (B : ℕ) (d : Inputs s) (_hcode : s.payload=B*3+0)
      (hp : ∀ op,1<d.stage.f → ActivePrefixStageRuntimeData.Packed (changePair d op) D)
      (ops : List (Op (Fin d.stage.slots))),
      (ActivePrefixStageNativePairSchedule.cost
        (ActivePrefixStageNativePairSchedule.stageCost (B:=B) D d hp) ops : ℝ)≤
        (ops.length : ℝ)*C*scale d := by
  obtain ⟨C,hC,h⟩ := pair_uniform_bound D
  refine ⟨C+1,by positivity,?_⟩
  intro s B d hcode hp ops
  exact ActivePrefixStagePairBudget.sum_bound d _ C
    (fun op => h s B d hcode op (hp op)) ops

/-- The exponent bound accompanies the actual native word executable, rather
than a caller-supplied execution or conversion contract. -/
theorem exists_bounded_stage_program (D : ℕ) :
    ∃ q, ∃ P : Program ActivePrefixStageNative.tapes q Networks.Shared50ModularControl.prime,
    ∃ C : ℝ,0<C ∧ ∀ (s : Shape) (B : ℕ) (d : Inputs s) (_hcode : s.payload=B*3+0)
      (hp : ∀ op,1<d.stage.f → ActivePrefixStageRuntimeData.Packed (changePair d op) D)
      (ops : List (Op (Fin d.stage.slots))) (xs : ActivePrefixStageNativeRows.Rows d B)
      (_hn : ∀ i j,xs i j≠blank),
      let time := ActivePrefixStageNativePairSchedule.cost
        (ActivePrefixStageNativePairSchedule.stageCost (B:=B) D d hp) ops
      (time : ℝ)≤(ops.length : ℝ)*C*scale d ∧
      HoareTime (ActivePrefixStageNativePairSchedule.program P ops)
        (fun w => w=ActivePrefixStageNativePairRun.bank d xs)
        (fun w => w=ActivePrefixStageNativePairRun.bank d (ActivePrefixStageNativePairSchedule.result d ops xs)) time := by
  obtain ⟨q,P,hP⟩ := ActivePrefixStageNativePairSchedule.exists_stage_program
  obtain ⟨C,hC,hbound⟩ := schedule_uniform_bound D
  refine ⟨q,P,C,hC,?_⟩
  intro s B d hcode hp ops xs hn
  exact ⟨hbound s B d hcode hp ops,hP D s B d hcode hp ops xs hn⟩

end
end IntegerMultBounds.Machine.ActivePrefixStageNativePairBudget
