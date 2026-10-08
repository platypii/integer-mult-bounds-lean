import IntegerMultBounds.Machine.FlatCoordinateStages
import IntegerMultBounds.Machine.SharedPayloadStageSkeleton

/-! Fixed rational operation descriptions instantiate actual coordinate stages
with canonical dimensional words. Their complete finite-state skeletons are
independent of the prime-power exponent and trailing record width. -/
namespace IntegerMultBounds.Machine.FlatCoordinateSchedule
open Networks
open ActualAffineScaling (modulus)
open Shared50ModularControl (prime)
noncomputable section
variable {d b W : ℕ}
local instance : Fact prime.Prime := ⟨Shared50ModularControl.prime_prime⟩
local instance : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩

/-- Only actual protected coefficients and syntactically earlier shift controls. -/
inductive Op (d : ℕ)
  | scale (target : Fin d) (r : ℚ) (occurs : Shared50AffineCoefficients.ScaleOccurs r)
  | shift (target control : Fin d) (earlier : control < target) (r : ℚ)
      (occurs : Shared50AffineCoefficients.Occurs r)

def Op.rational : Op d → OrderedAffine.Op (Fin d) ℚ
  | .scale t r _ => .scale t r
  | .shift t k _ r _ => .shift t k r

def Op.action (op : Op d) (b : ℕ) : OrderedAffine.Op (Fin d) (ZMod (modulus b)) :=
  OrderedAffine.mapOp (Swap.Modular.ratMod (modulus b)) op.rational

/-- Canonical input representation of a dimensional integer. This specifies
supplied descriptors; it does not assert a free physical descriptor constructor. -/
def bits (n : ℕ) : List Bool := GrowingCounterData.advance n []

@[simp] theorem bits_value (n : ℕ) : Counter.value (bits n) = n := by
  simp [bits,GrowingCounterData.advance_value,Counter.value]

theorem bits_canonical (n : ℕ) : GrowingCounterData.Canonical (bits n) :=
  GrowingCounterData.advance_canonical n [] (Or.inl rfl)

/-- The entire physical primitive stage, with no descriptor-validity premises. -/
def instantiate (op : Op d) (b W : ℕ) (hW : 0 < W) : FlatCoordinateStages.Stage d b W :=
  match op with
  | .scale t _r hr => FlatCoordinateStages.scale hr t hW
      (bits (FlatCoordinateLayout.suffixSize (Q := modulus b) (W := W) t))
      (bits (modulus b)) (bits (FlatCoordinateLayout.prefixSize (Q := modulus b) t))
      (bits_value _) (bits_value _) (bits_value _) (bits_canonical _) (bits_canonical _) (bits_canonical _)
  | .shift t k hk r hr => FlatCoordinateStages.shift r (Shared50AffineCoefficients.denominator_bound hr) t k hk hW
      (fun _ => bits b) (fun _ => bits_value _) (fun _ => bits_canonical _)
      (bits (FlatCoordinateLayout.suffixSize (Q := modulus b) (W := W) t))
      (bits (modulus b)) (bits ((modulus b)^t.val))
      (bits_value _) (bits_value _) (bits_value _) (bits_canonical _) (bits_canonical _) (bits_canonical _)

/-- Fixed finite-state control selected before any variable array dimensions. -/
def skeleton (op : Op d) : SharedPayloadStageSkeleton.Skeleton prime :=
  SharedPayloadStageSkeleton.ofStage (instantiate op 0 1 (by decide))

/-- The entire transition table, tape count, state count and payload wiring
are independent of the prime-power exponent and trailing record width. -/
theorem ofStage_instantiate (op : Op d) (b W : ℕ) (hW : 0 < W) :
    SharedPayloadStageSkeleton.ofStage (instantiate op b W hW) = skeleton op := by
  cases op <;> rfl

def Op.slope : Op d → ℕ
  | .scale _ r _ => 2064+120*(r.num.natAbs+r.den)
  | .shift t _ _ _ _ => 878+4*(t.val-1)

def Op.intercept : Op d → ℕ
  | .scale _ _ _ => 254
  | .shift t _ _ _ _ => 29*t.val+29

/-- Every initialization, arithmetic, data movement and normalization step is
included in the primitive's exact affine-in-volume time bound. -/
theorem instantiate_cost (op : Op d) (b W : ℕ) (hW : 0 < W) :
    (instantiate op b W hW).cost = op.slope*((modulus b)^d*W)+op.intercept := by
  cases op <;> rfl

/-- Concrete primitive output transports common-layout coordinates exactly as
the specialized rational operation, preserving the complete trailing record. -/
theorem instantiate_transport (op : Op d) (b W : ℕ) (hW : 0 < W)
    (a : FlatCoordinateStages.Array d b W) (x : Fin d → ZMod (modulus b)) (j : Fin W) :
    (instantiate op b W hW).transform a
      (FlatCoordinateLayout.index (OrderedAffine.execute (op.action b) x) j) =
        a (FlatCoordinateLayout.index x j) := by
  cases op with
  | scale t r hr => exact FlatCoordinateScaling.array_entry hr a t x j
  | shift t k hk r hr => exact FlatCoordinateShift.array_entry r a t k hk x j

/-- The syntactic conditions for translating an existing scalar schedule. -/
def Supported : OrderedAffine.Op (Fin d) ℚ → Prop
  | .scale _ r => Shared50AffineCoefficients.ScaleOccurs r
  | .shift t k r => k < t ∧ Shared50AffineCoefficients.Occurs r

def ofOp (op : OrderedAffine.Op (Fin d) ℚ) (h : Supported op) : Op d :=
  match op with
  | .scale t r => .scale t r h
  | .shift t k r => .shift t k h.1 r h.2

@[simp] theorem rational_ofOp (op : OrderedAffine.Op (Fin d) ℚ) (h : Supported op) :
    (ofOp op h).rational = op := by cases op <;> rfl

/-- Fixed-list conversion consumes only coefficient occurrence and target order;
all actual tape execution proofs are discharged by instantiate. -/
def ofList (ops : List (OrderedAffine.Op (Fin d) ℚ)) (h : ∀ op ∈ ops, Supported op) : List (Op d) :=
  ops.attach.map (fun op => ofOp op.val (h op.val op.property))

theorem rational_ofList (ops : List (OrderedAffine.Op (Fin d) ℚ)) (h : ∀ op ∈ ops, Supported op) :
    (ofList ops h).map Op.rational = ops := by
  simp [ofList,List.map_map]

end
end IntegerMultBounds.Machine.FlatCoordinateSchedule
