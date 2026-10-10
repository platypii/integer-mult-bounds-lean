import IntegerMultBounds.Machine.CompactComplexPhasePhysical
import IntegerMultBounds.Machine.ActivePrefixStageNativePairBudget

/-! The actual complex25 basis word compiles independently of runtime geometry.
Changing the finite slot type preserves the entire compiled machine, including
its state count: only the original numerical source and target indices are
used by the physical header writers. -/
namespace IntegerMultBounds.Machine.CompactComplexPhaseFixedWord
noncomputable section
open Networks.BinaryRowProgram (Op)
open Networks.Shared50ModularControl (prime)
open ActivePrefixStageNativePairSchedule (states program)

/-- Package the machine with its state count so equality includes both. -/
def compiled {q M : ℕ} (P : Program ActivePrefixStageNative.tapes q prime)
    (ops : List (Op (Fin M))) : Σ r, Program ActivePrefixStageNativePairSchedule.count r prime :=
  ⟨states P ops, program P ops⟩

theorem map_cast {q M N : ℕ} (P : Program ActivePrefixStageNative.tapes q prime)
    (h : M=N) (ops : List (Op (Fin M))) :
    compiled P (ops.map (CompactComplexPhaseSchedule.mapOp (finCongr h)))=compiled P ops := by
  subst N
  have he : CompactComplexPhaseSchedule.mapOp (finCongr (rfl : M=M))=id := by
    funext op
    cases op
    rfl
  rw [he,List.map_id]

def fixed {q : ℕ} (P : Program ActivePrefixStageNative.tapes q prime)
    (edge : Networks.ComplexPhaseRowSchedule.Edge) :=
  compiled P (Networks.ComplexPhaseRowSchedule.word edge)

theorem actual_eq_fixed {q : ℕ} (P : Program ActivePrefixStageNative.tapes q prime)
    {s : CompactGadgetReservationShape.Shape} (d : ActivePrefixStageFullData.Inputs s)
    (hslots : d.stage.slots=25^3) (edge : Networks.ComplexPhaseRowSchedule.Edge) :
    compiled P (CompactComplexPhasePhysical.word d hslots edge)=fixed P edge :=
  map_cast P hslots.symm _

theorem reverse_eq_fixed {q : ℕ} (P : Program ActivePrefixStageNative.tapes q prime)
    {s : CompactGadgetReservationShape.Shape} (d : ActivePrefixStageFullData.Inputs s)
    (hslots : d.stage.slots=25^3) (edge : Networks.ComplexPhaseRowSchedule.Edge) :
    compiled P (CompactComplexPhasePhysical.word d hslots edge).reverse=
      compiled P (Networks.ComplexPhaseRowSchedule.word edge).reverse := by
  unfold CompactComplexPhasePhysical.word CompactComplexPhaseSchedule.nodeWord
  rw [←List.map_reverse]
  exact map_cast P hslots.symm _

/-- A single native stage yields fixed forward and inverse machines for each
finite actual edge, uniformly over all runtime widths and original callers. -/
def Spec {q : ℕ} (D : ℕ) (P : Program ActivePrefixStageNative.tapes q prime) (C : ℝ) : Prop :=
    ∀ (s : CompactGadgetReservationShape.Shape) (B : ℕ)
      (d : ActivePrefixStageFullData.Inputs s) (hslots : d.stage.slots=25^3)
      (_hcode : s.payload=B*3+0)
      (hp : ∀ op,1<d.stage.f → ActivePrefixStageRuntimeData.Packed
        (ActivePrefixStagePairData.changePair d op) D)
      (edge : Networks.ComplexPhaseRowSchedule.Edge)
      (xs : ActivePrefixStageNativeRows.Rows d B) (_hn : ∀ i j,xs i j≠blank),
      let ops := CompactComplexPhasePhysical.word d hslots edge
      let forwardTime := ActivePrefixStageNativePairSchedule.cost
        (ActivePrefixStageNativePairSchedule.stageCost (B:=B) D d hp) ops
      let reverseTime := ActivePrefixStageNativePairSchedule.cost
        (ActivePrefixStageNativePairSchedule.stageCost (B:=B) D d hp) ops.reverse
      (forwardTime : ℝ)≤((Networks.ComplexPhaseRowSchedule.word edge).length : ℝ)*C*
        ActivePrefixStageInverseBudget.scale d ∧
      HoareTime (fixed P edge).2
        (fun z => z=ActivePrefixStageNativePairRun.bank d xs)
        (fun z => z=ActivePrefixStageNativePairRun.bank d
          (ActivePrefixStageNativePairSchedule.result d ops xs)) forwardTime ∧
      (reverseTime : ℝ)≤((Networks.ComplexPhaseRowSchedule.word edge).length : ℝ)*C*
        ActivePrefixStageInverseBudget.scale d ∧
      HoareTime (compiled P (Networks.ComplexPhaseRowSchedule.word edge).reverse).2
        (fun z => z=ActivePrefixStageNativePairRun.bank d xs)
        (fun z => z=ActivePrefixStageNativePairRun.bank d
          (ActivePrefixStageNativePairSchedule.result d ops.reverse xs)) reverseTime

theorem exists_fixed_program (D : ℕ) :
    ∃ q, ∃ P : Program ActivePrefixStageNative.tapes q prime, ∃ C : ℝ, 0<C ∧
    Spec D P C := by
  obtain ⟨q,P,C,hC,hP⟩ := ActivePrefixStageNativePairBudget.exists_bounded_stage_program D
  refine ⟨q,P,C,hC,?_⟩
  intro s B d hslots hcode hp edge xs hn
  let ops := CompactComplexPhasePhysical.word d hslots edge
  obtain ⟨hf,hrun⟩ := hP s B d hcode hp ops xs hn
  obtain ⟨hb,hback⟩ := hP s B d hcode hp ops.reverse xs hn
  have hl : ops.length=(Networks.ComplexPhaseRowSchedule.word edge).length := by
    simp [ops,CompactComplexPhasePhysical.word,CompactComplexPhaseSchedule.nodeWord]
  change HoareTime (compiled P ops).2 _ _ _ at hrun
  change HoareTime (compiled P ops.reverse).2 _ _ _ at hback
  rw [actual_eq_fixed P d hslots edge] at hrun
  rw [reverse_eq_fixed P d hslots edge] at hback
  rw [hl] at hf
  rw [List.length_reverse,hl] at hb
  exact ⟨hf,hrun,hb,hback⟩

end
end IntegerMultBounds.Machine.CompactComplexPhaseFixedWord
