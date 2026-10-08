import IntegerMultBounds.Machine.FlatCoordinateScheduleCompile
import IntegerMultBounds.Networks.AffineFieldCoordinates

/-! Actual Shared50 nonrecursive field operations become fixed concrete scalar
stage lists in one H-before-D coordinate layout. Recursive interchanges remain
explicitly excluded and require their separate physical realization. -/
namespace IntegerMultBounds.Machine.Shared50NonrecursiveCoordinates
open Networks
open Shared50ModularSchedule (Index)
open Shared50AffineControl (rationalSchedules)
open Shared50ModularControl (prime)
open FlatCoordinateSchedule
open AffineFieldCoordinates
open ActualAffineScaling (modulus)
noncomputable section

/-- The reflection coefficient is a genuine scale in the actual fixed pre-field
schedule; support is proved from occurrence, not added as a machine assumption. -/
theorem neg_one_scale_occurs : Shared50AffineCoefficients.ScaleOccurs (-1) := by
  have hw : Nonempty Shared50GlobalBudget.World := Fintype.card_pos_iff.mp (by
    rw [Shared50GlobalBudget.world_card]; decide)
  let w : Shared50GlobalBudget.World := Classical.choice hw
  have hpre : (Shared50FiniteInterchange.preFields : List (Swap.Shear.Op Index ℚ)) ∈
      Shared50FiniteInterchange.rationalFieldPrograms := by
    unfold Shared50FiniteInterchange.rationalFieldPrograms
    exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨w,Shared50GlobalTrace.mem_wires w,rfl⟩))
  let p := AffineFieldProgram.compile (Shared50FiniteInterchange.preFields : List (Swap.Shear.Op Index ℚ))
  have hp : p ∈ rationalSchedules := List.mem_map.mpr ⟨_,hpre,rfl⟩
  refine ⟨p,hp,(0 : Index),Or.inr ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨.transformD (-1),?_,?_⟩
  · simp [Shared50FiniteInterchange.preFields]
  · apply List.mem_map.mpr
    refine ⟨.scale (0 : Index) (-1),?_,rfl⟩
    apply List.mem_flatMap.mpr
    refine ⟨0,Swap.Shear.mem_descending _,?_⟩
    simp [OrderedAffine.row]

/-- Existing legality and coefficient occurrence discharge every concrete
scalar-stage precondition for an actual nonrecursive field operation. -/
theorem expanded_supported (p : List (AffineFieldProgram.Op Index ℚ)) (hp : p ∈ rationalSchedules)
    (op : AffineFieldProgram.Op Index ℚ) (hop : op ∈ p) (hn : Nonrecursive op) :
    ∀ out ∈ expand op, Supported out := by
  have hl := Shared50AffineControl.rational_schedules_legal p hp op hop
  cases op with
  | affineH op =>
    intro out hout
    have he : out = liftH op := by simpa only [expand,List.mem_singleton] using hout
    subst out
    cases op with
    | scale i r => exact ⟨p,hp,i,Or.inl hop⟩
    | shift i j r => exact ⟨hl,⟨p,hp,_,hop,rfl⟩⟩
  | affineD op =>
    intro out hout
    have he : out = liftD op := by simpa only [expand,List.mem_singleton] using hout
    subst out
    cases op with
    | scale i r => exact ⟨p,hp,i,Or.inr hop⟩
    | shift i j r =>
      refine ⟨?_,⟨p,hp,_,hop,rfl⟩⟩
      change 125000+j.val < 125000+i.val
      exact Nat.add_lt_add_left hl _
  | addToD i j =>
    intro out hout
    have he : out = .shift (dIndex j) (hIndex i) 1 := by simpa only [expand,List.mem_singleton] using hout
    subst out
    exact ⟨h_before_d i j,⟨p,hp,_,hop,rfl⟩⟩
  | subFromD i j =>
    intro out hout
    simp only [expand,List.mem_cons,List.not_mem_nil,or_false] at hout
    rcases hout with rfl | rfl
    · exact neg_one_scale_occurs
    · exact ⟨h_before_d i j,⟨p,hp,_,hop,Or.inl rfl⟩⟩
  | interchange i j => exact hn.elim

/-- Concrete fixed stage description for one actual nonrecursive operation. -/
def description (p : List (AffineFieldProgram.Op Index ℚ)) (hp : p ∈ rationalSchedules)
    (op : AffineFieldProgram.Op Index ℚ) (hop : op ∈ p) (hn : Nonrecursive op) :
    List (FlatCoordinateSchedule.Op (125000+125000)) :=
  ofList (expand op) (expanded_supported p hp op hop hn)

theorem description_rational (p : List (AffineFieldProgram.Op Index ℚ)) (hp : p ∈ rationalSchedules)
    (op : AffineFieldProgram.Op Index ℚ) (hop : op ∈ p) (hn : Nonrecursive op) :
    (description p hp op hop hn).map FlatCoordinateSchedule.Op.rational = expand op :=
  rational_ofList _ _

private theorem ratMod_neg_one (m : ℕ) : Swap.Modular.ratMod m (-1) = -1 := by
  simp [Swap.Modular.ratMod]

theorem description_actions (p : List (AffineFieldProgram.Op Index ℚ)) (hp : p ∈ rationalSchedules)
    (op : AffineFieldProgram.Op Index ℚ) (hop : op ∈ p) (hn : Nonrecursive op) (b : ℕ) :
    (description p hp op hop hn).map (fun op => op.action b) =
      expand (AffineFieldProgram.mapOp (Swap.Modular.ratMod (modulus b)) op) := by
  change (description p hp op hop hn).map
    ((OrderedAffine.mapOp (Swap.Modular.ratMod (modulus b))) ∘ FlatCoordinateSchedule.Op.rational) = _
  rw [← List.map_map,description_rational]
  exact expand_map _ (Swap.Modular.ratMod_one _) (ratMod_neg_one _) _

/-- The actual canonical output array has the exact H/D field semantics,
including reflected subtraction and every trailing record symbol. -/
theorem array_entry (p : List (AffineFieldProgram.Op Index ℚ)) (hp : p ∈ rationalSchedules)
    (op : AffineFieldProgram.Op Index ℚ) (hop : op ∈ p) (hn : Nonrecursive op)
    (b W : ℕ) (hW : 0 < W) (a : FlatCoordinateStages.Array (125000+125000) b W)
    (s : Swap.Shear.State Index (ZMod (modulus b))) (j : Fin W) :
    let _ : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩
    FlatCoordinateScheduleCompile.array (description p hp op hop hn) b W hW a
      (FlatCoordinateLayout.index
        (embed (AffineFieldProgram.execute (AffineFieldProgram.mapOp (Swap.Modular.ratMod (modulus b)) op) s)) j) =
      a (FlatCoordinateLayout.index (embed s) j) := by
  dsimp only
  have hm : Nonrecursive (AffineFieldProgram.mapOp (Swap.Modular.ratMod (modulus b)) op) := by
    cases op <;> exact hn
  have hh := FlatCoordinateScheduleCompile.array_entry (description p hp op hop hn) b W hW a (embed s) j
  rw [description_actions,expand_run _ hm] at hh
  exact hh


/-- A fixed physical program realizes each actual nonrecursive Shared50 field
operation at every prime-power width. Its linear constant depends only on the
fixed operation; the exact initial metadata contains supplied canonical dimensions. -/
theorem realizes (p : List (AffineFieldProgram.Op Index ℚ)) (hp : p ∈ rationalSchedules)
    (op : AffineFieldProgram.Op Index ℚ) (hop : op ∈ p) (hn : Nonrecursive op)
    (b W : ℕ) (hW : 0 < W) :
    let _ : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩
    let ops := description p hp op hop hn
    ∃ (input output : FlatCoordinateStages.Array (125000+125000) b W →
        Tapes (FlatCoordinateScheduleCompile.skeleton ops).tapes prime)
      (metadata : Tapes (FlatCoordinateScheduleCompile.skeleton ops).tapes prime),
      (∀ a, SharedPayload.payload (input a) (FlatCoordinateScheduleCompile.skeleton ops).source
        (FlatCoordinateScheduleCompile.skeleton ops).dest = FlatAffineScalingPayload.pair a) ∧
      (∀ a, SharedPayload.strip (input a) (FlatCoordinateScheduleCompile.skeleton ops).source
        (FlatCoordinateScheduleCompile.skeleton ops).dest = metadata) ∧
      (∀ a, HoareTime (FlatCoordinateScheduleCompile.skeleton ops).program (fun v => v = input a)
        (fun v => v = output a ∧
          SharedPayload.payload v (FlatCoordinateScheduleCompile.skeleton ops).source
            (FlatCoordinateScheduleCompile.skeleton ops).dest =
              FlatAffineScalingPayload.pair (FlatCoordinateScheduleCompile.array ops b W hW a) ∧
          ∀ (s : Swap.Shear.State Index (ZMod (modulus b))) (j : Fin W),
            FlatCoordinateScheduleCompile.array ops b W hW a
              (FlatCoordinateLayout.index (embed (AffineFieldProgram.execute
                (AffineFieldProgram.mapOp (Swap.Modular.ratMod (modulus b)) op) s)) j) =
                a (FlatCoordinateLayout.index (embed s) j))
        (FlatCoordinateScheduleCompile.constant ops*((modulus b)^(125000+125000)*W))) := by
  dsimp only
  obtain ⟨input,output,metadata,hi,hm,hh⟩ :=
    FlatCoordinateScheduleCompile.realizes (description p hp op hop hn) b W hW
  refine ⟨input,output,metadata,hi,hm,?_⟩
  intro a
  apply (hh a).consequence (fun _ h => h) ?_ le_rfl
  intro v hv
  exact ⟨hv.1,hv.2.1,array_entry p hp op hop hn b W hW a⟩

end
end IntegerMultBounds.Machine.Shared50NonrecursiveCoordinates
