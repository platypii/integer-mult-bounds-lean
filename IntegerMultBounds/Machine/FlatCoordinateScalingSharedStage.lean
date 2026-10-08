import IntegerMultBounds.Machine.FlatCoordinateScalingSharedBank
import IntegerMultBounds.Machine.SharedBankSkeleton

/-! A fully initialized actual affine scaling as a four-common-tape stage.
The sole original payload and b/W tapes are shared, with blank private input. -/
namespace IntegerMultBounds.Machine.FlatCoordinateScalingSharedStage
open Networks
open Networks.Shared50ModularControl (prime)
open ActualAffineScaling (modulus)
open FlatCoordinateLayout
noncomputable section
variable {d b W : ℕ}
local instance : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩

abbrev Stage (d b W : ℕ) := SharedBankStage.Stage (FlatCoordinateStages.Array d b W) 4 prime
  (FlatCoordinateShiftSharedBank.common (d := d) (b := b) (W := W))

def costCoefficient (r : ℚ) (t : Fin d) : ℕ :=
  24*t.val+24*suffixFields t+333+22*FlatAffineScalingInstall.LocalTapes r.num.natAbs r.den+
    (2064+120*(r.num.natAbs+r.den))+256

def stage (r : ℚ) (hr : Shared50AffineCoefficients.ScaleOccurs r) (t : Fin d)
    (b W : ℕ) (hW : 0 < W) : Stage d b W where
  tapes := _
  states := _
  program := FlatCoordinateScalingConstruct.program hr t
  transform := fun a => FlatCoordinateScaling.array hr a t
  input := fun a => FlatCoordinateScalingConstruct.input (r := r) a t
  output := fun a => FlatCoordinateScalingConstruct.output hr a t
  slots := FlatCoordinateScalingSharedBank.slots r
  slots_injective := FlatCoordinateScalingSharedBank.slots_injective r
  metadata := SharedBank.empty _ prime
  cost := costCoefficient r t*((modulus b)^d*W)
  input_payload := FlatCoordinateScalingSharedBank.input_common hr t
  output_payload := FlatCoordinateScalingSharedBank.output_common hr t
  strip_input := FlatCoordinateScalingSharedBank.input_blank t
  realizes := fun a => FlatCoordinateScalingConstruct.constructs_hoare hr a t hW

def skeleton (r : ℚ) (hr : Shared50AffineCoefficients.ScaleOccurs r) (t : Fin d) :
    SharedBankSkeleton.Skeleton 4 prime where
  tapes := _
  states := _
  program := FlatCoordinateScalingConstruct.program hr t
  slots := FlatCoordinateScalingSharedBank.slots r
  slots_injective := FlatCoordinateScalingSharedBank.slots_injective r

theorem stage_skeleton (r : ℚ) (hr : Shared50AffineCoefficients.ScaleOccurs r) (t : Fin d)
    (b W : ℕ) (hW : 0 < W) :
    SharedBankSkeleton.ofStage (stage r hr t b W hW) = skeleton r hr t := rfl

theorem metadata_empty (r : ℚ) (hr : Shared50AffineCoefficients.ScaleOccurs r) (t : Fin d)
    (b W : ℕ) (hW : 0 < W) :
    (stage r hr t b W hW).metadata = SharedBank.empty (stage r hr t b W hW).tapes prime := rfl

theorem stage_transport (r : ℚ) (hr : Shared50AffineCoefficients.ScaleOccurs r) (t : Fin d)
    (b W : ℕ) (hW : 0 < W) (a : FlatCoordinateStages.Array d b W)
    (x : Fin d → ZMod (modulus b)) (j : Fin W) :
    (stage r hr t b W hW).transform a
      (index (OrderedAffine.execute (.scale t (Swap.Modular.ratMod (modulus b) r)) x) j) = a (index x j) :=
  FlatCoordinateScaling.array_entry hr a t x j

end
end IntegerMultBounds.Machine.FlatCoordinateScalingSharedStage
