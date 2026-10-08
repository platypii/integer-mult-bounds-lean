import IntegerMultBounds.Machine.FlatCoordinateShiftInput

/-! The common-payload stage interface for a controlled shift whose complete
private dimensions and width family are physically constructed from b and W. -/
namespace IntegerMultBounds.Machine.FlatCoordinateShiftInitializedStage
open Networks
open Networks.Shared50ModularControl (prime)
open ActualAffineScaling (modulus)
open FlatCoordinateLayout
open FlatCoordinateShiftFromDimensions
noncomputable section
variable {d b W : ℕ}
local instance : Fact prime.Prime := ⟨Shared50ModularControl.prime_prime⟩
local instance : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩

/-- The private initial bank contains only b/W; all derived descriptors and
workspace are initially blank and their construction is included in the cost. -/
def stage (r : ℚ) (hr : Shared50AffineCoefficients.Occurs r) (t k : Fin d) (hk : k < t)
    (b W : ℕ) (hW : 0 < W) : FlatCoordinateStages.Stage d b W where
  tapes := _
  states := _
  program := FlatCoordinateShiftFromDimensions.program r t k
  transform := fun a => FlatCoordinateShift.array (radix := prime) r a t k hk
  input := FlatCoordinateShiftFromDimensions.input t b W
  output := FlatCoordinateShiftFromDimensions.output r hr t k hk b W hW
  source := FlatCoordinateShiftFromDimensions.sourceSlot t
  dest := FlatCoordinateShiftFromDimensions.destSlot t
  distinct := FlatCoordinateShiftInput.slots_distinct t
  metadata := SharedPayload.strip (FlatCoordinateShiftFromDimensions.input t b W (fun _ => blank)) (FlatCoordinateShiftFromDimensions.sourceSlot t) (FlatCoordinateShiftFromDimensions.destSlot t)
  cost := FlatCoordinateShiftFromDimensions.constant t*((modulus b)^d*W)
  input_payload := FlatCoordinateShiftInput.input_payload t
  output_payload := FlatCoordinateShiftFromDimensions.output_payload r hr t k hk b W hW
  strip_input := fun a => FlatCoordinateShiftInput.strip_input_eq t a (fun _ => blank)
  realizes := fun a => (FlatCoordinateShiftFromDimensions.realizes_hoare r hr t k hk b W hW a).consequence
    (fun _ h => h) (fun _ h => h.1) le_rfl

/-- The complete finite transition table is selected before b or W are known. -/
def skeleton (r : ℚ) (t k : Fin d) : SharedPayloadStageSkeleton.Skeleton prime where
  tapes := _
  states := _
  program := FlatCoordinateShiftFromDimensions.program r t k
  source := FlatCoordinateShiftFromDimensions.sourceSlot t
  dest := FlatCoordinateShiftFromDimensions.destSlot t
  distinct := FlatCoordinateShiftInput.slots_distinct t

theorem stage_skeleton (r : ℚ) (hr : Shared50AffineCoefficients.Occurs r) (t k : Fin d) (hk : k < t)
    (b W : ℕ) (hW : 0 < W) :
    SharedPayloadStageSkeleton.ofStage (stage r hr t k hk b W hW) = skeleton r t k := rfl

theorem stage_transport (r : ℚ) (hr : Shared50AffineCoefficients.Occurs r) (t k : Fin d) (hk : k < t)
    (b W : ℕ) (hW : 0 < W) (a : FlatCoordinateStages.Array d b W)
    (x : Fin d → ZMod (modulus b)) (j : Fin W) :
    (stage r hr t k hk b W hW).transform a
      (index (OrderedAffine.execute (.shift t k (Swap.Modular.ratMod (modulus b) r)) x) j) = a (index x j) :=
  FlatCoordinateShift.array_entry r a t k hk x j

end
end IntegerMultBounds.Machine.FlatCoordinateShiftInitializedStage
