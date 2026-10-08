import IntegerMultBounds.Machine.ActualAffineScaling
import IntegerMultBounds.Machine.SignedScalingDimensions

/-! Literal scaling for coefficients that actually occur in the fixed Shared50
ordered-affine schedules. Schedule membership discharges positivity and unit
conditions at every prime-power width. Program size depends only on the fixed
rational coefficient. Only canonical dimension words and declared scratch remain
inputs; the concrete bank still specifies the inherited fixed sentinels. This
module proves one complete fiber transform, not the full stream scheduler. -/
namespace IntegerMultBounds.Machine.ActualAffineScalingDimensions

open Networks
open Shared50ModularControl (prime)
open SignedScalingPrepared (Setup)
open SignedScalingDimensions (Scratch)

noncomputable section

open ActualAffineScaling (numerator_pos negative modulus modulus_pos outputBlocks
  outputBlocks_length outputBlocks_uniform outputBlocks_get)

abbrev TapeCount (r : ℚ) := SignedScalingDimensions.TapeCount r.num.natAbs r.den
abbrev States (r : ℚ) := 160+(ScalingPreparedExecution.SynthesisStates r.num.natAbs+
  ScalingPreparedExecution.SynthesisStates r.den+SignedScalingSign.states r.num.natAbs r.den (negative r))

/-- One literal finite program for the fixed actual coefficient, with no radix
exponent or block-width parameter in its transition table. -/
def program {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) : Program (TapeCount r) (States r) 0 :=
  SignedScalingDimensions.program (numerator_pos hr) r.den_pos (negative r)

def destinationSlot (r : ℚ) : Fin (TapeCount r) :=
  SignedScalingDimensions.destinationSlot r.num.natAbs r.den (negative r)

/-- The coefficient-dependent uniform constant, independent of radix width. -/
def linearConstant (r : ℚ) : ℕ := 1950+120*(r.num.natAbs+r.den)

def input {r : ℚ} (_hr : Shared50AffineCoefficients.ScaleOccurs r) (b : ℕ)
    (A : Setup r.num.natAbs) (D : Setup r.den) (S : Scratch)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ZMod (modulus b) → List (Fin 4)) : Tapes (TapeCount r) 0 :=
  SignedScalingDimensions.input (negative r) A D S (modulus b)
    source p middle s signMiddle t dest q (fun y => payload (y : ZMod (modulus b)))

def output {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) (b B : ℕ)
    (A : Setup r.num.natAbs) (D : Setup r.den) (S : Scratch)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ZMod (modulus b) → List (Fin 4)) : Tapes (TapeCount r) 0 :=
  SignedScalingDimensions.output (numerator_pos hr) r.den_pos (negative r) A D S (modulus b) B
    source p middle s signMiddle t dest q (fun y => payload (y : ZMod (modulus b)))

/-- Complete literal execution of an actual fixed scale, with all intermediate
scratch physically restored and every generated descriptor retained. All
tail and coefficient-piece descriptors are synthesized within the charged run. -/
theorem scaling_hoare {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) (b B : ℕ) (hB : 0 < B)
    (A : Setup r.num.natAbs) (D : Setup r.den) (S : Scratch)
    (hA : A.Valid (modulus b) B) (hD : D.Valid (modulus b) B)
    (hS : negative r = true → ∀ z, S.origin ≤ z →
      z < S.origin+(((modulus b-1)*B : ℕ) : ℤ) → S.tape z = blank)
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
  exact SignedScalingDimensions.scaling_hoare_linear (modulus_pos b) (numerator_pos hr) r.den_pos
    recipe.2.2.1 recipe.2.2.2.1 hB (negative r) A D S hA hD hS
    source p middle s signMiddle t dest q (fun y => payload (y : ZMod (modulus b)))
    (fun y => hwidth _) hblank hsblank

/-- The actual destination tape contains the complete signed coefficient recipe. -/
theorem output_tape {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) (b B : ℕ)
    (A : Setup r.num.natAbs) (D : Setup r.den) (S : Scratch)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ZMod (modulus b) → List (Fin 4)) :
    (output hr b B A D S source p middle s signMiddle t dest q payload).tape (destinationSlot r) =
      putWord dest q (outputBlocks hr b payload).flatten :=
  SignedScalingDimensions.output_tape (modulus_pos b) (numerator_pos hr) r.den_pos
    (Shared50AffineCoefficients.unit_recipe hr b).2.2.1 (negative r) A D S
    source p middle s signMiddle t dest q (fun y => payload (y : ZMod (modulus b)))

/-- Every symbol of every original block is present at its actual rational-scaled
physical destination, preserving the complete order inside the block. -/
theorem output_symbol {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) (b B : ℕ)
    (A : Setup r.num.natAbs) (D : Setup r.den) (S : Scratch)
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
    (A : Setup r.num.natAbs) (D : Setup r.den) (S : Scratch)
    (hA : A.Valid (modulus b) B) (hD : D.Valid (modulus b) B)
    (hS : negative r = true → ∀ z, S.origin ≤ z →
      z < S.origin+(((modulus b-1)*B : ℕ) : ℤ) → S.tape z = blank)
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
    (A : Setup r.num.natAbs) (D : Setup r.den) (S : Scratch)
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

/-- Exact full-bank execution and ordered-affine coordinates for every source
block in one target fiber. This does not assume or implement whole-grid scheduling. -/
theorem ordered_affine_hoare {ι : Type*} [LinearOrder ι] {r : ℚ}
    (hr : Shared50AffineCoefficients.ScaleOccurs r) (b B : ℕ) (hB : 0 < B)
    (A : Setup r.num.natAbs) (D : Setup r.den) (S : Scratch)
    (hA : A.Valid (modulus b) B) (hD : D.Valid (modulus b) B)
    (hS : negative r = true → ∀ z, S.origin ≤ z →
      z < S.origin+(((modulus b-1)*B : ℕ) : ℤ) → S.tape z = blank)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : (ι → ZMod (modulus b)) → List (Fin 4))
    (hwidth : ∀ x, (payload x).length = B) (address : ι → ZMod (modulus b)) (target : ι)
    (hblank : ∀ z, s ≤ z → z < s+((modulus b*B : ℕ) : ℤ) → middle z = blank)
    (hsblank : negative r = true → ∀ z, t ≤ z → z < t+((modulus b*B : ℕ) : ℤ) → signMiddle z = blank) :
    HoareTime (program hr)
      (fun v => v = input hr b A D S source p middle s signMiddle t dest q
        (fun z => payload (ScalingAffineBridge.fiber address target z)))
      (fun v => v = output hr b B A D S source p middle s signMiddle t dest q
          (fun z => payload (ScalingAffineBridge.fiber address target z)) ∧
        ∀ (x : ZMod (modulus b)) (k : ℕ) (hk : k < B),
          v.tape (destinationSlot r)
            (q+((((OrderedAffine.execute (.scale target (Swap.Modular.ratMod (modulus b) r))
              (ScalingAffineBridge.fiber address target x)) target).val*B+k : ℕ) : ℤ)) =
            (payload (ScalingAffineBridge.fiber address target x))[k]'(by rw [hwidth]; exact hk))
      (linearConstant r*(modulus b*B)) := by
  have hh := realizes_hoare hr b B hB A D S hA hD hS source p middle s signMiddle t dest q
    (fun z => payload (ScalingAffineBridge.fiber address target z)) (fun z => hwidth _) hblank hsblank
  simpa only [OrderedAffine.execute,ScalingAffineBridge.fiber,Function.update_self] using hh

/-- The physical negation scratch and its head return to their original state. -/
theorem output_scratch {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) (b B : ℕ)
    (A : Setup r.num.natAbs) (D : Setup r.den) (S : Scratch)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ZMod (modulus b) → List (Fin 4)) :
    let v := output hr b B A D S source p middle s signMiddle t dest q payload
    let slot := SignedScalingDimensions.scratchSlot r.num.natAbs r.den
    v.tape slot = S.tape ∧ v.head slot = S.origin :=
  SignedScalingDimensions.output_scratch (numerator_pos hr) r.den_pos (negative r) A D S (modulus b) B
    source p middle s signMiddle t dest q (fun y => payload (y : ZMod (modulus b)))

/-- Fixed tape and control-state counts, independent of radix exponent b and
payload block width B. Actual schedules choose r once, before execution. -/
theorem tapeCount_eq (r : ℚ) : TapeCount r = 49+4*(r.num.natAbs+r.den) :=
  SignedScalingDimensions.tapeCount_eq _ _

theorem stateCount_eq (r : ℚ) :
    States r = 117*(r.num.natAbs+r.den)+(if negative r then 787 else 455) :=
  SignedScalingDimensions.stateCount_eq _ _ _

end
end IntegerMultBounds.Machine.ActualAffineScalingDimensions
