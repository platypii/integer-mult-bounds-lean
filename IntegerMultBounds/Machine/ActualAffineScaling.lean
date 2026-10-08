import IntegerMultBounds.Machine.SignedScalingSign

/-! Literal scaling for coefficients that actually occur in the fixed Shared50
ordered-affine schedules. Schedule membership discharges positivity and unit
conditions at every prime-power width. Program size depends only on the fixed
rational coefficient; prepared descriptors and scratch conditions remain explicit. -/
namespace IntegerMultBounds.Machine.ActualAffineScaling

open Networks
open Shared50ModularControl (prime)
open SignedScalingExecution (Controls)
open SignedScalingSign (SignControls)

noncomputable section

/-- Width-independent numerator positivity, obtained from actual occurrence. -/
theorem numerator_pos {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) : 0 < r.num.natAbs :=
  (Shared50AffineCoefficients.unit_recipe hr 0).1

def negative (r : ℚ) : Bool := decide (r.num < 0)

def modulus (b : ℕ) : ℕ := prime^b

theorem modulus_pos (b : ℕ) : 0 < modulus b := pow_pos Shared50ModularControl.prime_prime.pos b

abbrev TapeCount (r : ℚ) := SignedScalingSign.TapeCount r.num.natAbs r.den
abbrev States (r : ℚ) := SignedScalingSign.states r.num.natAbs r.den (negative r)

/-- One literal finite program for the fixed actual coefficient, with no radix
exponent or block-width parameter in its transition table. -/
def program {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) : Program (TapeCount r) (States r) 0 :=
  SignedScalingSign.program (numerator_pos hr) r.den_pos (negative r)

def destinationSlot (r : ℚ) : Fin (TapeCount r) :=
  SignedScalingSign.destinationSlot r.num.natAbs r.den (negative r)

/-- The coefficient-dependent uniform constant, independent of radix width. -/
def linearConstant (r : ℚ) : ℕ := 1368+120*(r.num.natAbs+r.den)

def outputBlocks {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) (b : ℕ)
    (payload : ZMod (modulus b) → List (Fin 4)) : List (List (Fin 4)) :=
  ScalingAffineBridge.signedBlocks (numerator_pos hr) (modulus b) r.den (negative r)
    (fun y => payload (y : ZMod (modulus b)))

theorem outputBlocks_length {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) (b : ℕ)
    (payload : ZMod (modulus b) → List (Fin 4)) : (outputBlocks hr b payload).length = modulus b := by
  unfold outputBlocks ScalingAffineBridge.signedBlocks
  split_ifs <;> simp [ScalingAffineBridge.positiveBlocks]

theorem outputBlocks_uniform {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) (b B : ℕ)
    (payload : ZMod (modulus b) → List (Fin 4)) (hwidth : ∀ x, (payload x).length = B) :
    BlockRotationData.Uniform B (outputBlocks hr b payload) := by
  have hc : r.num.natAbs.Coprime (modulus b) := (Shared50AffineCoefficients.unit_recipe hr b).2.2.1
  unfold outputBlocks
  rw [ScalingAffineBridge.signedBlocks_modular _ _ _ hc]
  intro block hb
  obtain ⟨y,_,rfl⟩ := List.mem_map.mp hb
  exact hwidth _

/-- The actual ratMod forward destination carries precisely the original block. -/
theorem outputBlocks_get {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) (b : ℕ)
    (payload : ZMod (modulus b) → List (Fin 4)) (x : ZMod (modulus b)) :
    (outputBlocks hr b payload)[(Swap.Modular.ratMod (modulus b) r*x).val]? = some (payload x) :=
  ScalingAffineBridge.actual_signed_get hr b payload x

def input {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) (b : ℕ)
    (A : Controls r.num.natAbs) (D : Controls r.den) (S : SignControls)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ZMod (modulus b) → List (Fin 4)) : Tapes (TapeCount r) 0 :=
  SignedScalingSign.input (numerator_pos hr) (negative r) A D S (modulus b)
    source p middle s signMiddle t dest q (fun y => payload (y : ZMod (modulus b)))

def output {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) (b B : ℕ)
    (A : Controls r.num.natAbs) (D : Controls r.den) (S : SignControls)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ZMod (modulus b) → List (Fin 4)) : Tapes (TapeCount r) 0 :=
  SignedScalingSign.output (numerator_pos hr) r.den_pos (negative r) A D S (modulus b) B
    source p middle s signMiddle t dest q (fun y => payload (y : ZMod (modulus b)))

private theorem bound_le {r : ℚ} (b B : ℕ) (hB : 0 < B) :
    SignedScalingSign.bound (modulus b) B r.num.natAbs r.den (negative r) ≤
      linearConstant r*(modulus b*B) := by
  have hv : 1 ≤ modulus b*B := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.ne_of_gt (modulus_pos b)) (Nat.ne_of_gt hB))
  have hm := Nat.mul_le_mul_left (120*(r.num.natAbs+r.den)+516) hv
  unfold SignedScalingSign.bound linearConstant
  split_ifs <;> nlinarith

/-- Complete literal execution of an actual fixed scale, with all intermediate
scratch physically restored and every supplied immutable descriptor retained. -/
theorem scaling_hoare {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) (b B : ℕ) (hB : 0 < B)
    (A : Controls r.num.natAbs) (D : Controls r.den) (S : SignControls)
    (hA : A.Valid (modulus b) B) (hD : D.Valid (modulus b) B)
    (hS : negative r = true → S.Valid (modulus b) B)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ZMod (modulus b) → List (Fin 4))
    (hwidth : ∀ x, (payload x).length = B)
    (hblank : ∀ z, s ≤ z → z < s+((modulus b*B : ℕ) : ℤ) → middle z = blank)
    (hsblank : negative r = true → ∀ z, t ≤ z → z < t+((modulus b*B : ℕ) : ℤ) → signMiddle z = blank) :
    HoareTime (program hr)
      (fun v => v = input hr b A D S source p middle s signMiddle t dest q payload)
      (fun v => v = output hr b B A D S source p middle s signMiddle t dest q payload)
      (linearConstant r*(modulus b*B)) := by
  have recipe := Shared50AffineCoefficients.unit_recipe hr b
  exact (SignedScalingSign.scaling_hoare (modulus_pos b) (numerator_pos hr) r.den_pos
    recipe.2.2.1 recipe.2.2.2.1 hB (negative r) A D S hA hD hS
    source p middle s signMiddle t dest q (fun y => payload (y : ZMod (modulus b)))
    (fun y => hwidth _) hblank hsblank).consequence (fun _ h => h) (fun _ h => h) (bound_le b B hB)

/-- The actual destination tape contains the complete signed coefficient recipe. -/
theorem output_tape {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) (b B : ℕ)
    (A : Controls r.num.natAbs) (D : Controls r.den) (S : SignControls)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ZMod (modulus b) → List (Fin 4)) :
    (output hr b B A D S source p middle s signMiddle t dest q payload).tape (destinationSlot r) =
      putWord dest q (outputBlocks hr b payload).flatten :=
  SignedScalingSign.output_tape (modulus_pos b) (numerator_pos hr) r.den_pos
    (Shared50AffineCoefficients.unit_recipe hr b).2.2.1 (negative r) A D S
    source p middle s signMiddle t dest q (fun y => payload (y : ZMod (modulus b)))

/-- Every symbol of every original block is present at its actual rational-scaled
physical destination, preserving the complete order inside the block. -/
theorem output_symbol {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) (b B : ℕ)
    (A : Controls r.num.natAbs) (D : Controls r.den) (S : SignControls)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ZMod (modulus b) → List (Fin 4))
    (hwidth : ∀ x, (payload x).length = B) (x : ZMod (modulus b)) (k : ℕ) (hk : k < B) :
    (output hr b B A D S source p middle s signMiddle t dest q payload).tape (destinationSlot r)
      (q+(((Swap.Modular.ratMod (modulus b) r*x).val*B+k : ℕ) : ℤ)) =
      (payload x)[k]'(by rw [hwidth]; exact hk) := by
  rw [output_tape]
  have hb := outputBlocks_get hr b payload x
  obtain ⟨hi,hblock⟩ := List.getElem?_eq_some_iff.mp hb
  have hs := BlockRotationData.flatten_index B (outputBlocks hr b payload)
    (outputBlocks_uniform hr b B payload hwidth) _ k hi hk
  have hp : (payload x)[k]? = some ((payload x)[k]'(by rw [hwidth]; exact hk)) :=
    List.getElem?_eq_getElem _
  rw [hblock,hp] at hs
  obtain ⟨hindex,hvalue⟩ := List.getElem?_eq_some_iff.mp hs
  rw [WordSegments.get _ _ _ _ hindex,hvalue]

/-- Concrete tape execution and the actual scalar-address action in one Hoare
postcondition, with the fixed coefficient's uniform linear-volume bound. -/
theorem realizes_hoare {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) (b B : ℕ) (hB : 0 < B)
    (A : Controls r.num.natAbs) (D : Controls r.den) (S : SignControls)
    (hA : A.Valid (modulus b) B) (hD : D.Valid (modulus b) B)
    (hS : negative r = true → S.Valid (modulus b) B)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ZMod (modulus b) → List (Fin 4))
    (hwidth : ∀ x, (payload x).length = B)
    (hblank : ∀ z, s ≤ z → z < s+((modulus b*B : ℕ) : ℤ) → middle z = blank)
    (hsblank : negative r = true → ∀ z, t ≤ z → z < t+((modulus b*B : ℕ) : ℤ) → signMiddle z = blank) :
    HoareTime (program hr)
      (fun v => v = input hr b A D S source p middle s signMiddle t dest q payload)
      (fun v => v = output hr b B A D S source p middle s signMiddle t dest q payload ∧
        ∀ (x : ZMod (modulus b)) (k : ℕ) (hk : k < B),
          v.tape (destinationSlot r) (q+(((Swap.Modular.ratMod (modulus b) r*x).val*B+k : ℕ) : ℤ)) =
            (payload x)[k]'(by rw [hwidth]; exact hk))
      (linearConstant r*(modulus b*B)) := by
  apply (scaling_hoare hr b B hB A D S hA hD hS source p middle s signMiddle t dest q payload
    hwidth hblank hsblank).consequence (fun _ h => h) _ le_rfl
  rintro v rfl
  exact ⟨rfl,output_symbol hr b B A D S source p middle s signMiddle t dest q payload hwidth⟩


/-- Specialize opaque blocks to the complete address fiber. The physical
output position is exactly the target coordinate of OrderedAffine.execute. -/
theorem ordered_affine_symbol {ι : Type*} [LinearOrder ι] {r : ℚ}
    (hr : Shared50AffineCoefficients.ScaleOccurs r) (b B : ℕ)
    (A : Controls r.num.natAbs) (D : Controls r.den) (S : SignControls)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : (ι → ZMod (modulus b)) → List (Fin 4))
    (hwidth : ∀ x, (payload x).length = B) (address : ι → ZMod (modulus b)) (target : ι)
    (k : ℕ) (hk : k < B) :
    (output hr b B A D S source p middle s signMiddle t dest q
      (fun z => payload (ScalingAffineBridge.fiber address target z))).tape (destinationSlot r)
      (q+((((OrderedAffine.execute (.scale target (Swap.Modular.ratMod (modulus b) r)) address) target).val*B+k : ℕ) : ℤ)) =
      (payload address)[k]'(by rw [hwidth]; exact hk) := by
  have hh := output_symbol hr b B A D S source p middle s signMiddle t dest q
    (fun z => payload (ScalingAffineBridge.fiber address target z)) (fun z => hwidth _) (address target) k hk
  simpa only [OrderedAffine.execute,ScalingAffineBridge.fiber,Function.update_self,Function.update_eq_self] using hh

/-- Fixed tape and control-state counts, independent of radix exponent b and
payload block width B. Actual schedules choose r once, before execution. -/
theorem tapeCount_eq (r : ℚ) : TapeCount r = 38+4*(r.num.natAbs+r.den) :=
  SignedScalingSign.tapeCount_eq _ _

theorem stateCount_eq (r : ℚ) :
    States r = 98*(r.num.natAbs+r.den)+(if negative r then 545 else 213) :=
  SignedScalingSign.stateCount_eq _ _ _

end
end IntegerMultBounds.Machine.ActualAffineScaling
