import IntegerMultBounds.Machine.FlatCoordinateShiftSharedBank
import IntegerMultBounds.Machine.SharedBankSkeleton

/-! A completely initialized controlled shift as a four-common-tape stage.
The payload pair and sole b/W pair are permanent; every private input tape is
blank. A finite schedule can therefore share its two original headers directly. -/
namespace IntegerMultBounds.Machine.FlatCoordinateShiftSharedStage
open Networks
open Networks.Shared50ModularControl (prime)
open ActualAffineScaling (modulus)
open FlatCoordinateLayout
noncomputable section
variable {d b W : ℕ}
local instance : Fact prime.Prime := ⟨Shared50ModularControl.prime_prime⟩
local instance : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩

abbrev Stage (d b W : ℕ) := SharedBankStage.Stage (FlatCoordinateStages.Array d b W) 4 prime
  (FlatCoordinateShiftSharedBank.common (d := d) (b := b) (W := W))

def stage (r : ℚ) (hr : Shared50AffineCoefficients.Occurs r) (t k : Fin d) (hk : k < t)
    (b W : ℕ) (hW : 0 < W) : Stage d b W where
  tapes := _
  states := _
  program := FlatCoordinateShiftFromDimensions.program r t k
  transform := fun a => FlatCoordinateShift.array (radix := prime) r a t k hk
  input := FlatCoordinateShiftFromDimensions.input t b W
  output := FlatCoordinateShiftFromDimensions.output r hr t k hk b W hW
  slots := FlatCoordinateShiftSharedBank.slots t
  slots_injective := FlatCoordinateShiftSharedBank.slots_injective t
  metadata := SharedBank.empty _ prime
  cost := FlatCoordinateShiftFromDimensions.constant t*((modulus b)^d*W)
  input_payload := FlatCoordinateShiftSharedBank.input_common t
  output_payload := FlatCoordinateShiftSharedBank.output_common r hr t k hk hW
  strip_input := FlatCoordinateShiftSharedBank.input_blank t
  realizes := fun a => (FlatCoordinateShiftFromDimensions.realizes_hoare r hr t k hk b W hW a).consequence
    (fun _ h => h) (fun _ h => h.1) le_rfl

def skeleton (r : ℚ) (t k : Fin d) : SharedBankSkeleton.Skeleton 4 prime where
  tapes := _
  states := _
  program := FlatCoordinateShiftFromDimensions.program r t k
  slots := FlatCoordinateShiftSharedBank.slots t
  slots_injective := FlatCoordinateShiftSharedBank.slots_injective t

theorem stage_skeleton (r : ℚ) (hr : Shared50AffineCoefficients.Occurs r) (t k : Fin d) (hk : k < t)
    (b W : ℕ) (hW : 0 < W) :
    SharedBankSkeleton.ofStage (stage r hr t k hk b W hW) = skeleton r t k := rfl

theorem metadata_empty (r : ℚ) (hr : Shared50AffineCoefficients.Occurs r) (t k : Fin d) (hk : k < t)
    (b W : ℕ) (hW : 0 < W) :
    (stage r hr t k hk b W hW).metadata = SharedBank.empty (stage r hr t k hk b W hW).tapes prime := rfl

theorem stage_transport (r : ℚ) (hr : Shared50AffineCoefficients.Occurs r) (t k : Fin d) (hk : k < t)
    (b W : ℕ) (hW : 0 < W) (a : FlatCoordinateStages.Array d b W)
    (x : Fin d → ZMod (modulus b)) (j : Fin W) :
    (stage r hr t k hk b W hW).transform a
      (index (OrderedAffine.execute (.shift t k (Swap.Modular.ratMod (modulus b) r)) x) j) = a (index x j) :=
  FlatCoordinateShift.array_entry r a t k hk x j

end
end IntegerMultBounds.Machine.FlatCoordinateShiftSharedStage
