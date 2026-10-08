import IntegerMultBounds.Machine.ActualAffineScalingDimensions
import IntegerMultBounds.Machine.SignedScalingDimensionsStream

/-! Actual Shared50 rational scales on a physically consecutive family of equal
Q-by-B fibers. One fixed machine synthesizes metadata once, then runs the entire
counted family. The symbol theorem uses the concrete address i*Q*B+y*B+k. It does
not assert that an arbitrary multidimensional field layout already has this
fiber order. Canonical Q/B/n and inherited fixed sentinels remain explicit. -/
namespace IntegerMultBounds.Machine.ActualAffineScalingStream

open Networks
open SignedScalingPrepared (Setup)
open SignedScalingDimensions (Scratch)
open ActualAffineScaling (numerator_pos negative modulus modulus_pos outputBlocks
  outputBlocks_uniform outputBlocks_get)

noncomputable section

abbrev TapeCount (r : ℚ) := SignedScalingDimensionsStream.TapeCount r.num.natAbs r.den
abbrev States (r : ℚ) := SignedScalingDimensionsStream.States r.num.natAbs r.den (negative r)

/-- Independent of the radix exponent, block width and number of fibers. -/
def program {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) : Program (TapeCount r) (States r) 0 :=
  SignedScalingDimensionsStream.program (numerator_pos hr) r.den_pos (negative r)

def destinationSlot (r : ℚ) : Fin (TapeCount r) :=
  SignedScalingDimensionsStream.destinationSlot r.num.natAbs r.den (negative r)

def linearConstant (r : ℚ) : ℕ := 1381+120*(r.num.natAbs+r.den)
def nonemptyConstant (r : ℚ) : ℕ := 1737+120*(r.num.natAbs+r.den)

def input {r : ℚ} (_hr : Shared50AffineCoefficients.ScaleOccurs r) (b n : ℕ) (ns : List Bool)
    (A : Setup r.num.natAbs) (D : Setup r.den) (S : Scratch)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → ZMod (modulus b) → List (Fin 4)) : Tapes (TapeCount r) 0 :=
  SignedScalingDimensionsStream.input (negative r) A D S (modulus b) n ns source p middle s signMiddle t dest q
    (fun i y => payload i (y : ZMod (modulus b)))

def output {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) (b B n : ℕ) (ns : List Bool)
    (A : Setup r.num.natAbs) (D : Setup r.den) (S : Scratch)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → ZMod (modulus b) → List (Fin 4)) : Tapes (TapeCount r) 0 :=
  SignedScalingDimensionsStream.state (numerator_pos hr) r.den_pos (negative r) A D S (modulus b) B n ns
    source p middle s signMiddle t dest q (fun i y => payload i (y : ZMod (modulus b))) n

/-- Exact full-bank endpoint for actual coefficients, with once-only setup
charged even when there are no fibers. No derived descriptor is supplied. -/
theorem scaling_hoare {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) (b B n : ℕ) (hB : 0 < B)
    (ns : List Bool) (hn : Counter.value ns = n) (cn : GrowingCounterData.Canonical ns)
    (A : Setup r.num.natAbs) (D : Setup r.den) (S : Scratch)
    (hA : A.Valid (modulus b) B) (hD : D.Valid (modulus b) B)
    (hS : negative r = true → ∀ z, S.origin ≤ z → z < S.origin+(((modulus b-1)*B : ℕ) : ℤ) → S.tape z = blank)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → ZMod (modulus b) → List (Fin 4))
    (hwidth : ∀ i x, (payload i x).length = B)
    (hblank : ∀ z, s ≤ z → z < s+((modulus b*B : ℕ) : ℤ) → middle z = blank)
    (hsblank : negative r = true → ∀ z, t ≤ z → z < t+((modulus b*B : ℕ) : ℤ) → signMiddle z = blank) :
    HoareTime (program hr)
      (fun v => v = input hr b n ns A D S source p middle s signMiddle t dest q payload)
      (fun v => v = output hr b B n ns A D S source p middle s signMiddle t dest q payload)
      (linearConstant r*(n*(modulus b*B))+356*(modulus b*B)+249) := by
  have recipe := Shared50AffineCoefficients.unit_recipe hr b
  have hh := SignedScalingDimensionsStream.scaling_hoare (modulus_pos b) (numerator_pos hr) r.den_pos
    recipe.2.2.1 recipe.2.2.2.1 hB (negative r) A D S hA hD hS ns hn cn
    source p middle s signMiddle t dest q (fun i y => payload i (y : ZMod (modulus b))) (fun i y => hwidth i _) hblank hsblank
  rw [ScalingStream.source_length (modulus b) B n _ (fun i y => hwidth i _)] at hh
  exact hh

/-- Nonempty streams absorb descriptor synthesis into the complete payload. -/
theorem scaling_hoare_linear {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) (b B n : ℕ)
    (hB : 0 < B) (hnpos : 0 < n) (ns : List Bool) (hn : Counter.value ns = n) (cn : GrowingCounterData.Canonical ns)
    (A : Setup r.num.natAbs) (D : Setup r.den) (S : Scratch)
    (hA : A.Valid (modulus b) B) (hD : D.Valid (modulus b) B)
    (hS : negative r = true → ∀ z, S.origin ≤ z → z < S.origin+(((modulus b-1)*B : ℕ) : ℤ) → S.tape z = blank)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → ZMod (modulus b) → List (Fin 4))
    (hwidth : ∀ i x, (payload i x).length = B)
    (hblank : ∀ z, s ≤ z → z < s+((modulus b*B : ℕ) : ℤ) → middle z = blank)
    (hsblank : negative r = true → ∀ z, t ≤ z → z < t+((modulus b*B : ℕ) : ℤ) → signMiddle z = blank) :
    HoareTime (program hr)
      (fun v => v = input hr b n ns A D S source p middle s signMiddle t dest q payload)
      (fun v => v = output hr b B n ns A D S source p middle s signMiddle t dest q payload)
      (nonemptyConstant r*(n*(modulus b*B))+249) := by
  have recipe := Shared50AffineCoefficients.unit_recipe hr b
  have hh := SignedScalingDimensionsStream.scaling_hoare_linear (modulus_pos b) (numerator_pos hr) r.den_pos
    recipe.2.2.1 recipe.2.2.2.1 hB hnpos (negative r) A D S hA hD hS ns hn cn
    source p middle s signMiddle t dest q (fun i y => payload i (y : ZMod (modulus b))) (fun i y => hwidth i _) hblank hsblank
  rw [ScalingStream.source_length (modulus b) B n _ (fun i y => hwidth i _)] at hh
  exact hh

def outputPrefix {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) (b n : ℕ)
    (payload : ℕ → ZMod (modulus b) → List (Fin 4)) : List (Fin 4) :=
  ((List.range n).map (fun i => (outputBlocks hr b (payload i)).flatten)).flatten

theorem output_tape {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) (b B n : ℕ) (ns : List Bool)
    (A : Setup r.num.natAbs) (D : Setup r.den) (S : Scratch)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → ZMod (modulus b) → List (Fin 4)) :
    let v := output hr b B n ns A D S source p middle s signMiddle t dest q payload
    v.tape (destinationSlot r) = putWord dest q (outputPrefix hr b n payload) ∧
      v.head (destinationSlot r) = q+((n*(modulus b*B) : ℕ) : ℤ) :=
  SignedScalingDimensionsStream.state_destination (numerator_pos hr) r.den_pos (negative r) A D S (modulus b) B n ns
    source p middle s signMiddle t dest q (fun i y => payload i (y : ZMod (modulus b))) n

/-- Each source block is present in its original fiber, at the exact rationally
scaled inner coordinate, with its internal symbol order preserved. -/
theorem output_symbol {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) (b B n : ℕ) (ns : List Bool)
    (A : Setup r.num.natAbs) (D : Setup r.den) (S : Scratch)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → ZMod (modulus b) → List (Fin 4))
    (hwidth : ∀ i x, (payload i x).length = B) (i : ℕ) (hi : i < n) (x : ZMod (modulus b)) (k : ℕ) (hk : k < B) :
    (output hr b B n ns A D S source p middle s signMiddle t dest q payload).tape (destinationSlot r)
      (q+((i*(modulus b*B)+(Swap.Modular.ratMod (modulus b) r*x).val*B+k : ℕ) : ℤ)) =
      (payload i x)[k]'(by rw [hwidth]; exact hk) := by
  rw [(output_tape hr b B n ns A D S source p middle s signMiddle t dest q payload).1]
  have hb := outputBlocks_get hr b (payload i) x
  obtain ⟨hj,hblock⟩ := List.getElem?_eq_some_iff.mp hb
  have hs := BlockRotationData.flatten_index B (outputBlocks hr b (payload i))
    (outputBlocks_uniform hr b B (payload i) (hwidth i)) _ k hj hk
  have hp : (payload i x)[k]? = some ((payload i x)[k]'(by rw [hwidth]; exact hk)) := List.getElem?_eq_getElem _
  rw [hblock,hp] at hs
  let words := (List.range n).map (fun j => (outputBlocks hr b (payload j)).flatten)
  have hu : BlockRotationData.Uniform (modulus b*B) words := by
    intro word hw
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hw
    exact SignedScalingStream.block_volume (modulus_pos b) (numerator_pos hr)
      (Shared50AffineCoefficients.unit_recipe hr b).2.2.1 r.den (negative r)
      (fun y => payload j (y : ZMod (modulus b))) (fun y => hwidth j _)
  have hi' : i < words.length := by simpa [words] using hi
  let : NeZero (modulus b) := ⟨Nat.ne_of_gt (modulus_pos b)⟩
  have hval : (Swap.Modular.ratMod (modulus b) r*x).val < modulus b :=
    ZMod.val_lt _
  have hoff : (Swap.Modular.ratMod (modulus b) r*x).val*B+k < modulus b*B := by nlinarith
  have ho := BlockRotationData.flatten_index (modulus b*B) words hu i _ hi' hoff
  have hw : words[i] = (outputBlocks hr b (payload i)).flatten := by simp [words]
  rw [hw,hs] at ho
  obtain ⟨hindex,hvalue⟩ := List.getElem?_eq_some_iff.mp ho
  change (outputPrefix hr b n payload)[i*(modulus b*B)+((Swap.Modular.ratMod (modulus b) r*x).val*B+k)] = _ at hvalue
  have hindex' : i*(modulus b*B)+(Swap.Modular.ratMod (modulus b) r*x).val*B+k < (outputPrefix hr b n payload).length := by
    simpa only [Nat.add_assoc,words,outputPrefix] using hindex
  rw [WordSegments.get _ _ _ _ hindex']
  convert hvalue using 1
  congr 1
  omega

/-- Exact whole bank and all physical scaled symbol addresses in one contract. -/
theorem realizes_hoare {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) (b B n : ℕ) (hB : 0 < B)
    (ns : List Bool) (hn : Counter.value ns = n) (cn : GrowingCounterData.Canonical ns)
    (A : Setup r.num.natAbs) (D : Setup r.den) (S : Scratch)
    (hA : A.Valid (modulus b) B) (hD : D.Valid (modulus b) B)
    (hS : negative r = true → ∀ z, S.origin ≤ z → z < S.origin+(((modulus b-1)*B : ℕ) : ℤ) → S.tape z = blank)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → ZMod (modulus b) → List (Fin 4))
    (hwidth : ∀ i x, (payload i x).length = B)
    (hblank : ∀ z, s ≤ z → z < s+((modulus b*B : ℕ) : ℤ) → middle z = blank)
    (hsblank : negative r = true → ∀ z, t ≤ z → z < t+((modulus b*B : ℕ) : ℤ) → signMiddle z = blank) :
    HoareTime (program hr)
      (fun v => v = input hr b n ns A D S source p middle s signMiddle t dest q payload)
      (fun v => v = output hr b B n ns A D S source p middle s signMiddle t dest q payload ∧
        ∀ (i : ℕ), i < n → ∀ (x : ZMod (modulus b)) (k : ℕ) (hk : k < B),
          v.tape (destinationSlot r)
            (q+((i*(modulus b*B)+(Swap.Modular.ratMod (modulus b) r*x).val*B+k : ℕ) : ℤ)) =
            (payload i x)[k]'(by rw [hwidth]; exact hk))
      (linearConstant r*(n*(modulus b*B))+356*(modulus b*B)+249) := by
  apply (scaling_hoare hr b B n hB ns hn cn A D S hA hD hS source p middle s signMiddle t dest q payload
    hwidth hblank hsblank).consequence (fun _ h => h) _ le_rfl
  rintro v rfl
  exact ⟨rfl,output_symbol hr b B n ns A D S source p middle s signMiddle t dest q payload hwidth⟩

/-- Ordered-affine semantics for an explicitly represented family of fibers.
The outer offset remains i*Q*B; only the declared inner target coordinate moves. -/
theorem ordered_affine_symbol {ι : Type*} [LinearOrder ι] {r : ℚ}
    (hr : Shared50AffineCoefficients.ScaleOccurs r) (b B n : ℕ) (ns : List Bool)
    (A : Setup r.num.natAbs) (D : Setup r.den) (S : Scratch)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → (ι → ZMod (modulus b)) → List (Fin 4))
    (hwidth : ∀ i address, (payload i address).length = B) (addresses : ℕ → ι → ZMod (modulus b)) (target : ι)
    (i : ℕ) (hi : i < n) (x : ZMod (modulus b)) (k : ℕ) (hk : k < B) :
    (output hr b B n ns A D S source p middle s signMiddle t dest q
      (fun j z => payload j (ScalingAffineBridge.fiber (addresses j) target z))).tape (destinationSlot r)
      (q+((i*(modulus b*B)+((OrderedAffine.execute (.scale target (Swap.Modular.ratMod (modulus b) r))
        (ScalingAffineBridge.fiber (addresses i) target x)) target).val*B+k : ℕ) : ℤ)) =
      (payload i (ScalingAffineBridge.fiber (addresses i) target x))[k]'(by rw [hwidth]; exact hk) := by
  have hh := output_symbol hr b B n ns A D S source p middle s signMiddle t dest q
    (fun j z => payload j (ScalingAffineBridge.fiber (addresses j) target z)) (fun j z => hwidth j _) i hi x k hk
  simpa only [OrderedAffine.execute,ScalingAffineBridge.fiber,Function.update_self] using hh

/-- Complete physical execution of the represented fiber family with exact
bank and ordered-affine action. No external field-layout identification is used. -/
theorem ordered_affine_hoare {ι : Type*} [LinearOrder ι] {r : ℚ}
    (hr : Shared50AffineCoefficients.ScaleOccurs r) (b B n : ℕ) (hB : 0 < B)
    (ns : List Bool) (hn : Counter.value ns = n) (cn : GrowingCounterData.Canonical ns)
    (A : Setup r.num.natAbs) (D : Setup r.den) (S : Scratch)
    (hA : A.Valid (modulus b) B) (hD : D.Valid (modulus b) B)
    (hS : negative r = true → ∀ z, S.origin ≤ z → z < S.origin+(((modulus b-1)*B : ℕ) : ℤ) → S.tape z = blank)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → (ι → ZMod (modulus b)) → List (Fin 4))
    (hwidth : ∀ i address, (payload i address).length = B) (addresses : ℕ → ι → ZMod (modulus b)) (target : ι)
    (hblank : ∀ z, s ≤ z → z < s+((modulus b*B : ℕ) : ℤ) → middle z = blank)
    (hsblank : negative r = true → ∀ z, t ≤ z → z < t+((modulus b*B : ℕ) : ℤ) → signMiddle z = blank) :
    HoareTime (program hr)
      (fun v => v = input hr b n ns A D S source p middle s signMiddle t dest q
        (fun j z => payload j (ScalingAffineBridge.fiber (addresses j) target z)))
      (fun v => v = output hr b B n ns A D S source p middle s signMiddle t dest q
          (fun j z => payload j (ScalingAffineBridge.fiber (addresses j) target z)) ∧
        ∀ (i : ℕ), i < n → ∀ (x : ZMod (modulus b)) (k : ℕ) (hk : k < B),
          v.tape (destinationSlot r)
            (q+((i*(modulus b*B)+((OrderedAffine.execute (.scale target (Swap.Modular.ratMod (modulus b) r))
              (ScalingAffineBridge.fiber (addresses i) target x)) target).val*B+k : ℕ) : ℤ)) =
            (payload i (ScalingAffineBridge.fiber (addresses i) target x))[k]'(by rw [hwidth]; exact hk))
      (linearConstant r*(n*(modulus b*B))+356*(modulus b*B)+249) := by
  have hh := realizes_hoare hr b B n hB ns hn cn A D S hA hD hS source p middle s signMiddle t dest q
    (fun j z => payload j (ScalingAffineBridge.fiber (addresses j) target z)) (fun j z => hwidth j _) hblank hsblank
  simpa only [OrderedAffine.execute,ScalingAffineBridge.fiber,Function.update_self] using hh

theorem tapeCount_eq (r : ℚ) : TapeCount r = 51+4*(r.num.natAbs+r.den) :=
  SignedScalingDimensionsStream.tapeCount_eq _ _

theorem stateCount_eq (r : ℚ) :
    States r = 117*(r.num.natAbs+r.den)+(if negative r then 803 else 471) :=
  SignedScalingDimensionsStream.stateCount_eq _ _ _

end
end IntegerMultBounds.Machine.ActualAffineScalingStream
