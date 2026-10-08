import IntegerMultBounds.Machine.SharedPayloadStage
import IntegerMultBounds.Machine.FlatCoordinateScaling
import IntegerMultBounds.Machine.FlatCoordinateShift
import IntegerMultBounds.Machine.FlatAffineScalingMetadata
import IntegerMultBounds.Machine.FlatControlledShiftMetadata

/-! Concrete shared-alphabet stages for the common ordered-coordinate array.
Each stage contains an actual program and discharged payload, metadata and time
contracts, ready for finite-list physical assembly. -/
namespace IntegerMultBounds.Machine.FlatCoordinateStages
open Networks
open ActualAffineScaling (modulus)
open Shared50ModularControl (prime)
open FlatCoordinateLayout
noncomputable section
variable {d b W : ℕ}
local instance : Fact prime.Prime := ⟨Shared50ModularControl.prime_prime⟩
local instance : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩

abbrev Array (d b W : ℕ) := Fin ((modulus b)^d*W) → Fin 4

abbrev Stage (d b W : ℕ) :=
  SharedPayloadStage.Stage (Array d b W) prime (FlatAffineScalingPayload.pair (radix := prime))

private theorem pair_word {n m : ℕ} (a : Fin n → Fin 4) (a' : Fin m → Fin 4)
    (h : List.ofFn a = List.ofFn a') :
    FlatAffineScalingPayload.pair (radix := prime) a = FlatAffineScalingPayload.pair a' := by
  unfold FlatAffineScalingPayload.pair
  rw [h]

/-- An actual occurring network scale, including alphabet lifting, blank-workspace
initialization, normalization and payload-independent private metadata. -/
def scale {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) (t : Fin d) (hW : 0 < W)
    (bs qs ns : List Bool) (hb : Counter.value bs = suffixSize (Q := modulus b) (W := W) t)
    (hq : Counter.value qs = modulus b) (hn : Counter.value ns = prefixSize (Q := modulus b) t)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cn : GrowingCounterData.Canonical ns) : Stage d b W where
  tapes := _
  states := _
  program := FlatAffineScalingPayload.program hr
  transform := fun a => FlatCoordinateScaling.array hr a t
  input := fun a => FlatAffineScalingPayload.input hr (fiberView a t) bs qs ns
  output := fun a => FlatAffineScalingPayload.output hr (fiberView a t) bs qs ns
  source := FlatAffineScaling.sourceSlot r
  dest := ActualAffineScalingStream.destinationSlot r
  distinct := FlatAffineScalingPayload.slots_distinct r
  metadata := SharedPayload.strip
    (FlatAffineScalingPayload.input hr (fiberView (fun _ => blank : Array d b W) t) bs qs ns)
    (FlatAffineScaling.sourceSlot r) (ActualAffineScalingStream.destinationSlot r)
  cost := (2064+120*(r.num.natAbs+r.den))*((modulus b)^d*W)+254
  input_payload := by
    intro a
    rw [FlatAffineScalingPayload.input_payload]
    exact pair_word _ _ (fiberView_word a t)
  output_payload := by
    intro a
    rw [FlatAffineScalingPayload.output_payload]
    exact pair_word _ _ (FlatCoordinateScaling.array_word hr a t).symm
  strip_input := by
    intro a
    exact FlatAffineScalingMetadata.strip_input_eq hr _ _ bs qs ns
  realizes := by
    intro a
    have hs := FlatAffineScalingPayload.realizes_hoare (radix := prime) hr (fiberView a t)
      (Nat.mul_pos (pow_pos (ActualAffineScaling.modulus_pos b) _) hW)
      (pow_pos (ActualAffineScaling.modulus_pos b) _) bs qs ns hb hq hn cb cq cn
    apply hs.consequence (fun _ h => h) (fun _ h => h) ?_
    rw [split_volume t]

/-- Canonical payload transport of the actual scaling stage. -/
theorem scale_transform {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) (t : Fin d) (hW : 0 < W)
    (bs qs ns : List Bool) (hb : Counter.value bs = suffixSize (Q := modulus b) (W := W) t)
    (hq : Counter.value qs = modulus b) (hn : Counter.value ns = prefixSize (Q := modulus b) t)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cn : GrowingCounterData.Canonical ns) (a : Array d b W) (x : Fin d → ZMod (modulus b)) (j : Fin W) :
    (scale hr t hW bs qs ns hb hq hn cb cq cn).transform a
      (index (OrderedAffine.execute (.scale t (Swap.Modular.ratMod (modulus b) r)) x) j) = a (index x j) :=
  FlatCoordinateScaling.array_entry hr a t x j

/-- A legal earlier-control rational shift, using exactly the earlier coordinates
as initialized prefix fields and discharging the physical control-slice equation. -/
def shift (r : ℚ) (hden : r.den < prime) (t k : Fin d) (hk : k < t) (hW : 0 < W)
    (ws : Fin ((t.val-1)+1) → List Bool)
    (hw : ∀ i, Counter.value (ws i) = b) (cw : ∀ i, GrowingCounterData.Canonical (ws i))
    (bs qs ns : List Bool) (hb : Counter.value bs = suffixSize (Q := modulus b) (W := W) t)
    (hq : Counter.value qs = modulus b) (hn : Counter.value ns = (modulus b)^t.val)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cn : GrowingCounterData.Canonical ns) : Stage d b W where
  tapes := _
  states := _
  program := FlatControlledShiftReady.program r
    (FlatCoordinateShift.low t k++0::FlatCoordinateShift.high t k) (by simp)
  transform := fun a => FlatCoordinateShift.array r a t k hk
  input := fun a => RationalPrefixTranslationBootstrap.input r
    (FlatCoordinateShift.low t k++0::FlatCoordinateShift.high t k) (fun _ => b) ws
    (FlatCoordinateShift.view a t k hk) (fun _ => blank) (fun _ => blank) 0 0 bs qs ns
  output := fun a => FlatControlledShiftReady.output r
    (FlatCoordinateShift.low t k) (FlatCoordinateShift.high t k) (fun _ => b) ws
    (FlatCoordinateShift.view a t k hk) (fun _ => blank) (fun _ => blank) 0 0 bs qs ns
  source := FlatControlledShiftPayload.sourceSlot (t.val-1)
  dest := FlatControlledShiftPayload.destSlot (t.val-1)
  distinct := FlatControlledShiftPayload.slots_ne (t.val-1)
  metadata := SharedPayload.strip (RationalPrefixTranslationBootstrap.input r
    (FlatCoordinateShift.low t k++0::FlatCoordinateShift.high t k) (fun _ => b) ws
    (FlatCoordinateShift.view (radix := prime) (fun _ => blank : Array d b W) t k hk)
    (fun _ => blank) (fun _ => blank) 0 0 bs qs ns)
    (FlatControlledShiftPayload.sourceSlot (t.val-1)) (FlatControlledShiftPayload.destSlot (t.val-1))
  cost := (878+4*(t.val-1))*((modulus b)^d*W)+29*t.val+29
  input_payload := by
    intro a
    dsimp only [Array,modulus] at a ⊢
    rw [FlatControlledShiftPayload.input_payload]
    rw [FlatCoordinateShift.view_word]
    unfold FlatArrayNormalize.pair FlatAffineScalingPayload.pair
    congr 1
    funext i; fin_cases i <;> rfl
  output_payload := by
    intro a
    dsimp only [Array,modulus] at a ⊢
    rw [FlatControlledShiftPayload.output_payload]
    rw [← FlatCoordinateShift.array_word]
    unfold FlatArrayNormalize.pair FlatAffineScalingPayload.pair
    congr 1
    funext i; fin_cases i <;> rfl
  strip_input := by
    intro a
    exact FlatControlledShiftMetadata.strip_input_eq r _ _ ws _ _ _ _ 0 0 bs qs ns
  realizes := by
    intro a
    have hs := FlatCoordinateShift.realizes_hoare r hden a t k hk hW ws hw cw
      (fun _ => blank) (fun _ => blank) 0 0 bs qs ns hb hq hn cb cq cn (by intros; rfl)
    exact hs.consequence (fun _ h => h) (fun _ h => h.1) le_rfl

/-- Canonical payload transport of the actual controlled-shift stage. -/
theorem shift_transform (r : ℚ) (hden : r.den < prime) (t k : Fin d) (hk : k < t) (hW : 0 < W)
    (ws : Fin ((t.val-1)+1) → List Bool)
    (hw : ∀ i, Counter.value (ws i) = b) (cw : ∀ i, GrowingCounterData.Canonical (ws i))
    (bs qs ns : List Bool) (hb : Counter.value bs = suffixSize (Q := modulus b) (W := W) t)
    (hq : Counter.value qs = modulus b) (hn : Counter.value ns = (modulus b)^t.val)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cn : GrowingCounterData.Canonical ns) (a : Array d b W) (x : Fin d → ZMod (modulus b)) (j : Fin W) :
    (shift r hden t k hk hW ws hw cw bs qs ns hb hq hn cb cq cn).transform a
      (index (OrderedAffine.execute (.shift t k (Swap.Modular.ratMod (modulus b) r)) x) j) = a (index x j) :=
  FlatCoordinateShift.array_entry r a t k hk x j

end
end IntegerMultBounds.Machine.FlatCoordinateStages
