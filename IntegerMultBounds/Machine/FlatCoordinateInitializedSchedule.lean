import IntegerMultBounds.Machine.FlatCoordinateScalingSharedStage
import IntegerMultBounds.Machine.FlatCoordinateShiftSharedStage
import IntegerMultBounds.Machine.SharedBankStageInput

/-! A fixed mixed affine coordinate schedule implemented from one input array,
one exponent and one trailing-width descriptor, with all private storage blank.
Four permanent tapes carry the payload pair and the sole preserved headers.
All dimension generation, descriptor copies, actual operations and joins are
charged, and the finite transition table is independent of variable dimensions. -/
namespace IntegerMultBounds.Machine.FlatCoordinateInitializedSchedule
open Networks
open Networks.Shared50ModularControl (prime)
open ActualAffineScaling (modulus)
open FlatCoordinateLayout
open FlatCoordinateSchedule (Op)
noncomputable section
variable {d b W : ℕ}
local instance : Fact prime.Prime := ⟨Shared50ModularControl.prime_prime⟩
local instance : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩

/-- Actual fully initialized stages, never supplied with a derived dimension. -/
def instantiate (op : Op d) (b W : ℕ) (hW : 0 < W) : FlatCoordinateShiftSharedStage.Stage d b W :=
  match op with
  | .scale t r hr => FlatCoordinateScalingSharedStage.stage r hr t b W hW
  | .shift t k hk r hr => FlatCoordinateShiftSharedStage.stage r hr t k hk b W hW

def opSkeleton : Op d → SharedBankSkeleton.Skeleton 4 prime
  | .scale t r hr => FlatCoordinateScalingSharedStage.skeleton r hr t
  | .shift t k _ r _ => FlatCoordinateShiftSharedStage.skeleton r t k

def coefficient : Op d → ℕ
  | .scale t r _ => FlatCoordinateScalingSharedStage.costCoefficient r t
  | .shift t _ _ _ _ => FlatCoordinateShiftFromDimensions.constant t

theorem instantiate_skeleton (op : Op d) (b W : ℕ) (hW : 0 < W) :
    SharedBankSkeleton.ofStage (instantiate op b W hW) = opSkeleton op := by
  cases op <;> rfl

theorem instantiate_blank (op : Op d) (b W : ℕ) (hW : 0 < W) :
    (instantiate op b W hW).metadata = SharedBank.empty (instantiate op b W hW).tapes prime := by
  cases op <;> rfl

theorem instantiate_cost (op : Op d) (b W : ℕ) (hW : 0 < W) :
    (instantiate op b W hW).cost = coefficient op*((modulus b)^d*W) := by
  cases op <;> rfl

theorem instantiate_transport (op : Op d) (b W : ℕ) (hW : 0 < W)
    (a : FlatCoordinateStages.Array d b W) (x : Fin d → ZMod (modulus b)) (j : Fin W) :
    (instantiate op b W hW).transform a (index (OrderedAffine.execute (op.action b) x) j) = a (index x j) := by
  cases op with
  | scale t r hr => exact FlatCoordinateScalingSharedStage.stage_transport r hr t b W hW a x j
  | shift t k hk r hr => exact FlatCoordinateShiftSharedStage.stage_transport r hr t k hk b W hW a x j

/-- Fixed machine data is chosen from the rational schedule alone. -/
def skeleton (ops : List (Op d)) : SharedBankSkeleton.Skeleton 4 prime :=
  SharedBankSkeleton.compile 4 prime (by decide) (ops.map opSkeleton)

/-- All four permanent tapes are literally the first four physical slots. -/
theorem skeleton_slots_val (ops : List (Op d)) (i : Fin 4) :
    ((skeleton ops).slots i).val = i.val := by cases ops <;> rfl

theorem skeleton_tapes_ge (ops : List (Op d)) : 4 ≤ (skeleton ops).tapes := by
  cases ops with
  | nil => rfl
  | cons op ops => change 4 ≤ 4+(opSkeleton op).tapes+(skeleton ops).tapes; omega

def stages (ops : List (Op d)) (b W : ℕ) (hW : 0 < W) := ops.map (fun op => instantiate op b W hW)

def stage (ops : List (Op d)) (b W : ℕ) (hW : 0 < W) :=
  SharedBankStage.compile (FlatCoordinateShiftSharedBank.common (d := d) (b := b) (W := W)) (by decide)
    (stages ops b W hW)

theorem stage_skeleton (ops : List (Op d)) (b W : ℕ) (hW : 0 < W) :
    SharedBankSkeleton.ofStage (stage ops b W hW) = skeleton ops := by
  unfold stage skeleton
  rw [SharedBankSkeleton.ofStage_compile]
  congr 1
  unfold stages
  simp only [List.map_map]
  apply List.map_congr_left
  intro op _
  exact instantiate_skeleton op b W hW

def array (ops : List (Op d)) (b W : ℕ) (hW : 0 < W) (a : FlatCoordinateStages.Array d b W) :=
  SharedBankStage.execute (stages ops b W hW) a

theorem array_entry (ops : List (Op d)) (b W : ℕ) (hW : 0 < W)
    (a : FlatCoordinateStages.Array d b W) (x : Fin d → ZMod (modulus b)) (j : Fin W) :
    array ops b W hW a (index (OrderedAffine.run (ops.map (fun op => op.action b)) x) j) = a (index x j) := by
  induction ops generalizing a x with
  | nil => rfl
  | cons op ops ih =>
    change array ops b W hW ((instantiate op b W hW).transform a)
      (index (OrderedAffine.run (ops.map (fun op => op.action b)) (OrderedAffine.execute (op.action b) x)) j) = _
    rw [ih]
    exact instantiate_transport op b W hW a x j

def constant (ops : List (Op d)) : ℕ := (ops.map coefficient).sum+ops.length

theorem costs_sum (ops : List (Op d)) (b W : ℕ) (hW : 0 < W) :
    ((stages ops b W hW).map SharedBankStage.Stage.cost).sum =
      (ops.map coefficient).sum*((modulus b)^d*W) := by
  induction ops with
  | nil => simp [stages]
  | cons op ops ih =>
    change (instantiate op b W hW).cost+((stages ops b W hW).map SharedBankStage.Stage.cost).sum = _
    rw [instantiate_cost,ih]
    simp only [List.map_cons,List.sum_cons,Nat.add_mul]

theorem stage_cost (ops : List (Op d)) (b W : ℕ) (hW : 0 < W) :
    (stage ops b W hW).cost = (ops.map coefficient).sum*((modulus b)^d*W)+ops.length := by
  unfold stage
  rw [SharedBankStage.compile_cost,costs_sum]
  simp only [stages,List.length_map]

theorem cost_le (ops : List (Op d)) (b W : ℕ) (hW : 0 < W) :
    (stage ops b W hW).cost ≤ constant ops*((modulus b)^d*W) := by
  rw [stage_cost]
  have hv : 0 < (modulus b)^d*W := Nat.mul_pos (pow_pos (ActualAffineScaling.modulus_pos b) _) hW
  have hh := Nat.le_mul_of_pos_right ops.length hv
  unfold constant
  nlinarith

/-- The initial bank is literal: array/scratch/b/W in the first four slots,
and every other tape blank at head zero. No per-stage descriptor is supplied. -/
def input (ops : List (Op d)) (b W : ℕ) (a : FlatCoordinateStages.Array d b W) :
    Tapes (skeleton ops).tapes prime :=
  SharedBankStageInput.raw (FlatCoordinateShiftSharedBank.common a) (skeleton ops).tapes

/-- One previously fixed program realizes the entire mixed affine schedule.
All private dimensions are physically generated, the sole b/W pair is preserved,
and the final canonical array realizes every scalar operation at every address. -/
theorem realizes (ops : List (Op d)) (b W : ℕ) (hW : 0 < W) :
    ∃ output : FlatCoordinateStages.Array d b W → Tapes (skeleton ops).tapes prime,
      ∀ a, HoareTime (skeleton ops).program
        (fun v => v = SharedBankStageInput.raw (FlatCoordinateShiftSharedBank.common a) (skeleton ops).tapes)
        (fun v => v = output a ∧
          SharedBank.payload v (skeleton ops).slots =
            FlatCoordinateShiftSharedBank.common (array ops b W hW a) ∧
          ∀ (x : Fin d → ZMod (modulus b)) (j : Fin W),
            array ops b W hW a (index (OrderedAffine.run (ops.map (fun op => op.action b)) x) j) = a (index x j))
        (constant ops*((modulus b)^d*W)) := by
  have hb : ∀ s ∈ stages ops b W hW, s.metadata = SharedBank.empty s.tapes prime := by
    intro s hs
    obtain ⟨op,_,rfl⟩ := List.mem_map.mp hs
    exact instantiate_blank op b W hW
  obtain ⟨output,hh⟩ := SharedBankStageInput.fixed_compile_hoare (by decide : 0 < 4)
    (stages ops b W hW) hb (skeleton ops) (stage_skeleton ops b W hW)
  refine ⟨output,?_⟩
  intro a
  apply (hh a).consequence (fun _ h => h) ?_ ?_
  · intro v hv
    exact ⟨hv.1,hv.2,array_entry ops b W hW a⟩
  · rw [← SharedBankStage.compile_cost (by decide : 0 < 4)]
    exact cost_le ops b W hW

end
end IntegerMultBounds.Machine.FlatCoordinateInitializedSchedule