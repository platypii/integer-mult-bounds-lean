import IntegerMultBounds.Machine.FlatCoordinateSchedule

/-! A fixed finite rational coordinate schedule compiles to one actual multitape
machine, independent of all variable array dimensions. Its private inputs are
canonical dimensional words; all writable storage starts blank. The two common
payload tapes carry the canonical array from stage to stage, and every physical
setup, motion, cleanup and sequential join is charged. -/
namespace IntegerMultBounds.Machine.FlatCoordinateScheduleCompile
open Networks
open ActualAffineScaling (modulus)
open Shared50ModularControl (prime)
open FlatCoordinateLayout
open FlatCoordinateSchedule (Op instantiate)
noncomputable section
variable {d b W : ℕ}
local instance : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩

/-- The transition table is selected once from the rational schedule alone. -/
def skeleton (ops : List (Op d)) : SharedPayloadStageSkeleton.Skeleton prime :=
  SharedPayloadStageSkeleton.compile prime (ops.map FlatCoordinateSchedule.skeleton)

def stages (ops : List (Op d)) (b W : ℕ) (hW : 0 < W) :=
  ops.map (fun op => instantiate op b W hW)

def stage (ops : List (Op d)) (b W : ℕ) (hW : 0 < W) :=
  SharedPayloadStage.compile (FlatAffineScalingPayload.pair (radix := prime)) (stages ops b W hW)

/-- Stage compilation has exactly the previously fixed machine skeleton. -/
theorem stage_skeleton (ops : List (Op d)) (b W : ℕ) (hW : 0 < W) :
    SharedPayloadStageSkeleton.ofStage (stage ops b W hW) = skeleton ops := by
  unfold stage skeleton
  rw [SharedPayloadStageSkeleton.ofStage_compile]
  congr 1
  unfold stages
  simp only [List.map_map]
  apply List.map_congr_left
  intro op _
  exact FlatCoordinateSchedule.ofStage_instantiate op b W hW

def array (ops : List (Op d)) (b W : ℕ) (hW : 0 < W) (a : FlatCoordinateStages.Array d b W) :=
  SharedPayloadStage.execute (stages ops b W hW) a

/-- Composition of the actual complete-array outputs transports every address
through the ordered rational schedule and preserves each trailing symbol. -/
theorem array_entry (ops : List (Op d)) (b W : ℕ) (hW : 0 < W)
    (a : FlatCoordinateStages.Array d b W) (x : Fin d → ZMod (modulus b)) (j : Fin W) :
    array ops b W hW a (index (OrderedAffine.run (ops.map (fun op => op.action b)) x) j) =
      a (index x j) := by
  induction ops generalizing a x with
  | nil => rfl
  | cons op ops ih =>
    change array ops b W hW ((instantiate op b W hW).transform a)
      (index (OrderedAffine.run (ops.map (fun op => op.action b)) (OrderedAffine.execute (op.action b) x)) j) = _
    rw [ih]
    exact FlatCoordinateSchedule.instantiate_transport op b W hW a x j

/-- Exact affine-in-volume budget, including every compiler join. -/
def budget (ops : List (Op d)) (volume : ℕ) : ℕ :=
  (ops.map (fun op => op.slope*volume+op.intercept)).sum+ops.length

def constant (ops : List (Op d)) : ℕ :=
  (ops.map (fun op => op.slope+op.intercept+1)).sum

theorem stage_cost (ops : List (Op d)) (b W : ℕ) (hW : 0 < W) :
    (stage ops b W hW).cost = budget ops ((modulus b)^d*W) := by
  unfold stage
  rw [SharedPayloadStage.compile_cost]
  unfold budget stages
  simp only [List.map_map,List.length_map]
  congr 2
  apply List.map_congr_left
  intro op _
  exact FlatCoordinateSchedule.instantiate_cost op b W hW

theorem budget_le (ops : List (Op d)) (volume : ℕ) (hv : 0 < volume) :
    budget ops volume ≤ constant ops*volume := by
  induction ops with
  | nil => simp [budget,constant]
  | cons op ops ih =>
    have hh : op.intercept+1 ≤ (op.intercept+1)*volume := Nat.le_mul_of_pos_right _ hv
    have hstep : op.slope*volume+op.intercept+1 ≤ (op.slope+op.intercept+1)*volume := by
      nlinarith
    change op.slope*volume+op.intercept+(ops.map (fun op => op.slope*volume+op.intercept)).sum+(ops.length+1) ≤ _
    change _ ≤ (op.slope+op.intercept+1+constant ops)*volume
    dsimp only [budget] at ih
    nlinarith

/-- One fixed machine realizes the whole schedule for every exponent and
positive record width. No running-time or stage-implementation hypothesis is
assumed. Canonical supplied descriptors are part of the exact initial banks. -/
theorem realizes (ops : List (Op d)) (b W : ℕ) (hW : 0 < W) :
    ∃ (input output : FlatCoordinateStages.Array d b W → Tapes (skeleton ops).tapes prime)
      (metadata : Tapes (skeleton ops).tapes prime),
      (∀ a, SharedPayload.payload (input a) (skeleton ops).source (skeleton ops).dest =
        FlatAffineScalingPayload.pair a) ∧
      (∀ a, SharedPayload.strip (input a) (skeleton ops).source (skeleton ops).dest = metadata) ∧
      (∀ a, HoareTime (skeleton ops).program (fun v => v = input a)
        (fun v => v = output a ∧
          SharedPayload.payload v (skeleton ops).source (skeleton ops).dest =
            FlatAffineScalingPayload.pair (array ops b W hW a) ∧
          ∀ (x : Fin d → ZMod (modulus b)) (j : Fin W),
            array ops b W hW a (index (OrderedAffine.run (ops.map (fun op => op.action b)) x) j) = a (index x j))
        (constant ops*((modulus b)^d*W))) := by
  obtain ⟨input,output,metadata,hi,hm,hh⟩ := SharedPayloadStageSkeleton.fixed_program
    (stage ops b W hW) (skeleton ops) (stage_skeleton ops b W hW)
  refine ⟨input,output,metadata,hi,hm,?_⟩
  intro a
  apply (hh a).consequence (fun _ h => h) ?_ ?_
  · intro v hv
    refine ⟨hv.1,?_,array_entry ops b W hW a⟩
    simpa only [stage,SharedPayloadStage.compile_transform,array] using hv.2
  · rw [stage_cost]
    exact budget_le ops _ (Nat.mul_pos (pow_pos (ActualAffineScaling.modulus_pos b) _) hW)

end
end IntegerMultBounds.Machine.FlatCoordinateScheduleCompile
