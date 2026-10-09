import IntegerMultBounds.Machine.ActivePrefixStageNativePairCoordinates
import IntegerMultBounds.Machine.ActivePrefixStageNativePairBudget

/-! Reversing a literal native basis word physically undoes every original
row permutation. Clean pair-frame endpoints permit exact chronological
composition; inverse conversion, descriptor and join costs are all paid. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageNativePairInverse
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageNativeRows (Rows)
open ActivePrefixStageNativePairRun (action bank)
open ActivePrefixStageNativePairSchedule (result cost stageCost)
open ActivePrefixStagePairData (changePair)
open Networks.BinaryRowProgram (Op)
variable {s : Shape} {B : ℕ}

theorem action_involutive (d : Inputs s) (op : Op (Fin d.stage.slots)) :
    Function.Involutive (action (B:=B) d op) := by
  intro xs
  funext i j
  change xs (ActivePrefixStageNativeRows.rowDestination (changePair d op)
    (ActivePrefixStageNativeRows.rowDestination (changePair d op) i)) j=xs i j
  rw [ActivePrefixStageNativePairCoordinates.row_destination_involutive d op i]

theorem result_append (d : Inputs s) (u v : List (Op (Fin d.stage.slots))) (xs : Rows d B) :
    result d (u++v) xs=result d v (result d u xs) := by
  induction u generalizing xs with
  | nil => rfl
  | cons op ops ih => exact ih (action d op xs)

theorem reverse_restores (d : Inputs s) (ops : List (Op (Fin d.stage.slots))) (xs : Rows d B) :
    result d ops.reverse (result d ops xs)=xs := by
  induction ops generalizing xs with
  | nil => rfl
  | cons op ops ih =>
    rw [List.reverse_cons,result_append]
    change action d op (result d ops.reverse (result d ops (action d op xs)))=xs
    rw [ih]
    exact action_involutive d op xs

theorem cost_reverse {M : ℕ} (bounds : Op (Fin M) → ℕ) (ops : List (Op (Fin M))) :
    cost bounds ops.reverse=cost bounds ops := by simp [cost,List.map_reverse]

def pairProgram {q M : ℕ} (P : Program ActivePrefixStageNative.tapes q Networks.Shared50ModularControl.prime)
    (ops : List (Op (Fin M))) :=
  seq (ActivePrefixStageNativePairSchedule.program P ops)
    (ActivePrefixStageNativePairSchedule.program P ops.reverse)

/-- The actual native executable, not an assumed reversible callback, supplies
both directions and the certified complete roundtrip budget. -/
theorem exists_roundtrip_stage_program (D : ℕ) :
    ∃ q, ∃ P : Program ActivePrefixStageNative.tapes q Networks.Shared50ModularControl.prime,
    ∃ C : ℝ,0<C ∧ ∀ (s : Shape) (B : ℕ) (d : Inputs s) (_hcode : s.payload=B*3+0)
      (hp : ∀ op,1<d.stage.f → ActivePrefixStageRuntimeData.Packed (changePair d op) D)
      (ops : List (Op (Fin d.stage.slots))) (xs : Rows d B) (_hn : ∀ i j,xs i j≠blank),
      let time := cost (stageCost (B:=B) D d hp) ops
      ((2*time+1 : ℕ) : ℝ)≤((ops.length : ℝ)*C+1)*ActivePrefixStageInverseBudget.scale d ∧
      HoareTime (pairProgram P ops) (fun w => w=bank d xs) (fun w => w=bank d xs) (2*time+1) := by
  obtain ⟨q,P,C,hC,hP⟩ := ActivePrefixStageNativePairBudget.exists_bounded_stage_program D
  refine ⟨q,P,2*C,by positivity,?_⟩
  intro s B d hcode hp ops xs hn
  obtain ⟨hb,hf⟩ := hP s B d hcode hp ops xs hn
  obtain ⟨_,hr⟩ := hP s B d hcode hp ops.reverse (result d ops xs)
    (ActivePrefixStageNativePairSchedule.result_nonblank d ops xs hn)
  rw [reverse_restores,cost_reverse] at hr
  refine ⟨?_,(hf.seq hr).consequence (fun _ h => h) (fun _ h => h) (by omega)⟩
  have hu := ActivePrefixStageInverseBudget.one_le_scale d
  push_cast
  nlinarith only [hb,hu]

end
end IntegerMultBounds.Machine.ActivePrefixStageNativePairInverse
