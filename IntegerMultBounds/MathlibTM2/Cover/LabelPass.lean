module

public import IntegerMultBounds.MathlibTM2.Cover.LabelAddress
public import IntegerMultBounds.Machine.FlatCoordinateCleanSchedule

/-! A fixed clean tape program for a rational lower-triangular label pass. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.LabelPass
noncomputable section

open IntegerMultBounds.Machine IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.M8.AtomOps
open IntegerMultBounds.Swap.Modular
open FlatCoordinateSchedule
open ActualAffineScaling (modulus)
open LabelAddress (pass)
variable {m : ℕ}
local instance (b : ℕ) : NeZero (modulus b) := ⟨(ActualAffineScaling.modulus_pos b).ne'⟩

/-- Only the diagonal scales and strictly lower shifts need coefficient certificates. -/
theorem supported (E : Matrix (Fin m) (Fin m) ℚ)
    (hd : ∀ i, Shared50AffineCoefficients.ScaleOccurs (E i i))
    (hl : ∀ i j, j < i → Shared50AffineCoefficients.Occurs (E i j)) :
    ∀ op ∈ pass E, Supported op := by
  intro op hop
  obtain ⟨a, ha, hop⟩ := List.mem_flatMap.mp hop
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ha
  rcases OrderedAffine.coefficient_origin E o ho with ⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩
  · obtain ⟨l, _, rfl⟩ := List.mem_map.mp hop
    exact hd i
  · obtain ⟨l, _, rfl⟩ := List.mem_map.mp hop
    exact ⟨at_lt hij l l, hl i j hij⟩

/-- The fixed rational pass moves each label to its right product and preserves its payload.
All work tapes are clean at both ends of the run. -/
theorem realizes (E : Matrix (Fin m) (Fin m) ℚ)
    (hs : ∀ op ∈ pass E, Supported op) (b W : ℕ) (hW : 0 < W)
    (hE : IntegerMultBounds.Swap.Shear.LowerTriangular E)
    (hu : IsUnit (reduce (modulus b) E))
    (a : FlatCoordinateStages.Array (m*m) b W) :
    let ops := ofList (pass E) hs
    let out := FlatCoordinateInitializedSchedule.array ops b W hW a
    HoareTime (FlatCoordinateCleanSchedule.program ops)
      (fun v => v = SharedBankStageInput.raw (FlatCoordinateShiftSharedBank.common a)
        (FlatCoordinateCleanSchedule.tapeCount ops))
      (fun v => v = SharedBankStageInput.raw (FlatCoordinateShiftSharedBank.common out)
          (FlatCoordinateCleanSchedule.tapeCount ops) ∧
        ∀ (g : Matrix (Fin m) (Fin m) (ZMod (modulus b))) (j : Fin W),
          out (finProdFinEquiv (LabelAddress.address (g * (reduce (modulus b) E).transpose), j)) =
            a (finProdFinEquiv (LabelAddress.address g, j)))
      (FlatCoordinateCleanSchedule.constant ops * ((modulus b)^(m*m)*W)) := by
  dsimp only
  apply (FlatCoordinateCleanSchedule.realizes (ofList (pass E) hs) b W hW a).consequence
    (fun _ h => h) ?_ le_rfl
  intro v hv
  refine ⟨hv.1, fun g j => ?_⟩
  have h := hv.2 (refine (Route.cols g)) j
  have hmap : ((ofList (pass E) hs).map fun op => op.action b) = pass (reduce (modulus b) E) := by
    rw [reduce, LabelAddress.pass_map]
    simpa only [List.map_map, Function.comp_def, Op.action] using
      congrArg (List.map (OrderedAffine.mapOp (ratMod (modulus b)))) (rational_ofList (pass E) hs)
  rw [hmap] at h
  have hl := reduce_lowerTriangular (modulus b) hE
  have hi := LabelAddress.pass_index hl (OrderedAffine.program_legal hl hu) g j
  convert h using 2
  apply Fin.ext
  simpa only [finProdFinEquiv_apply_val, Nat.mul_comm, Nat.add_comm] using hi.symm
  rfl

end
end IntegerMultBounds.MathlibTM2.Cover.LabelPass
