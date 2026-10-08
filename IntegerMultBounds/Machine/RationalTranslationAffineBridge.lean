import IntegerMultBounds.Machine.RationalTranslationStream
import IntegerMultBounds.Machine.WordSegments
import IntegerMultBounds.Networks.OrderedAffine
import IntegerMultBounds.Networks.Shared50AffineCoefficients

/-! Physical symbol transport for the concrete rational-controlled fiber stream.
The represented cyclic control value determines an OrderedAffine.shift target.
This proves the address action on the represented fiber layout; construction and
composition of a complete multidimensional layout remain separate obligations. -/
namespace IntegerMultBounds.Machine.RationalTranslationAffineBridge

open Networks
open TranslationStream (blocks)

private theorem uniform_blocks (Q B i : ℕ) (payload : ℕ → ℕ → List (Fin 4))
    (hwidth : ∀ i y, (payload i y).length = B) : BlockRotationData.Uniform B (blocks Q (payload i)) := by
  intro block hb
  obtain ⟨y,_,rfl⟩ := List.mem_map.mp hb
  exact hwidth i y

/-- Every source payload symbol occurs at its literal translated stream address. -/
theorem prefix_entry (a : ℕ → ℕ) (Q B n i y k : ℕ) (payload : ℕ → ℕ → List (Fin 4))
    (hwidth : ∀ i y, (payload i y).length = B) (hi : i < n) (hy : y < Q) (hk : k < B) :
    (TranslationPreparedFamily.outputPrefix a Q n payload)[i*(Q*B)+((y+a i)%Q)*B+k]? =
      some ((payload i y)[k]'(by rw [hwidth]; exact hk)) := by
  let words := (List.range n).map (fun j => (BlockRotationData.rotate (a j) (blocks Q (payload j))).flatten)
  have hu : BlockRotationData.Uniform (Q*B) words := by
    intro w hw
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hw
    rw [BlockRotationData.rotated_volume (a j) B _ (uniform_blocks Q B j payload hwidth)]
    simp [blocks]
  have hi' : i < words.length := by simpa [words] using hi
  have hm : (y+a i)%Q < Q := Nat.mod_lt _ (by omega)
  have hj : ((y+a i)%Q)*B+k < Q*B := by nlinarith
  have hout := BlockRotationData.flatten_index (Q*B) words hu i (((y+a i)%Q)*B+k) hi' hj
  have hin := BlockRotationData.payload_destination_entry (a i) B (blocks Q (payload i))
    (uniform_blocks Q B i payload hwidth) y k (by simpa [blocks] using hy) hk
  simp only [blocks,List.length_map,List.length_range,List.getElem_map,List.getElem_range] at hin
  simp only [words,List.getElem_map,List.getElem_range,blocks] at hout
  rw [hin] at hout
  simpa only [TranslationPreparedFamily.outputPrefix,words,blocks,Nat.add_assoc] using hout

variable {radix : ℕ} [Fact radix.Prime]

/-- Projection of the final physical stream bank onto its encoded destination. -/
theorem destination_tape (r : ℚ) (B n : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ)
    (bs qs ns old : List Bool) (xs : List (Fin radix)) (payload : ℕ → ℕ → List (Fin 4)) :
    (CountedLoopReuseAlphabet.bank
      (RationalTranslationStream.state r B n source dest p q bs qs old xs payload n)
      CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1).tape 11 =
      fun z => (RadixToBinary.binaryEncoding (q := radix)).encode
        (putWord dest q (RationalTranslationStream.outputPrefix r xs n payload) z) := rfl

/-- Exact symbol transport, including fiber number and the coordinate within its block. -/
theorem output_symbol_nat (r : ℚ) (B n : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ)
    (bs qs ns old : List Bool) (xs : List (Fin radix)) (payload : ℕ → ℕ → List (Fin 4))
    (hwidth : ∀ i y, (payload i y).length = B) (i y k : ℕ) (hi : i < n) (hy : y < radix^xs.length) (hk : k < B) :
    (CountedLoopReuseAlphabet.bank
      (RationalTranslationStream.state r B n source dest p q bs qs old xs payload n)
      CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1).tape 11
      (q+((i*(radix^xs.length*B)+((y+RationalTranslationStream.offset r xs i)%(radix^xs.length))*B+k : ℕ) : ℤ)) =
      (RadixToBinary.binaryEncoding (q := radix)).encode ((payload i y)[k]'(by rw [hwidth]; exact hk)) := by
  rw [destination_tape]
  have hs := prefix_entry (RationalTranslationStream.offset r xs) (radix^xs.length) B n i y k payload hwidth hi hy hk
  obtain ⟨hj,hvalue⟩ := List.getElem?_eq_some_iff.mp hs
  simp only [RationalTranslationStream.outputPrefix]
  rw [WordSegments.get _ _ _ _ hj,hvalue]

/-- Integer-address reduction agrees with addition in the modular target coordinate. -/
private theorem destination_index (Q : ℕ) [NeZero Q] (a : ℕ) (y : ZMod Q) :
    (y.val+a)%Q = (y+(a : ZMod Q)).val := by
  rw [ZMod.val_add,ZMod.val_natCast]
  exact (Nat.add_mod_mod y.val a Q).symm

/-- Physical destination agrees with the concrete rational address action. -/
theorem output_symbol (r : ℚ) (hden : r.den < radix) (B n : ℕ)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns old : List Bool) (xs : List (Fin radix))
    (payload : ℕ → ZMod (radix^xs.length) → List (Fin 4))
    (hwidth : ∀ i y, (payload i y).length = B) (i : ℕ) (y : ZMod (radix^xs.length)) (k : ℕ)
    (hi : i < n) (hk : k < B) :
    (CountedLoopReuseAlphabet.bank
      (RationalTranslationStream.state r B n source dest p q bs qs old xs
        (fun j z => payload j (z : ZMod (radix^xs.length))) n)
      CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1).tape 11
      (q+((i*(radix^xs.length*B)+
        (y+Swap.Modular.ratMod (radix^xs.length) r*((RadixDigits.value xs+i : ℕ) : ZMod (radix^xs.length))).val*B+k : ℕ) : ℤ)) =
      (RadixToBinary.binaryEncoding (q := radix)).encode ((payload i y)[k]'(by rw [hwidth]; exact hk)) := by
  let : NeZero (radix^xs.length) := ⟨pow_ne_zero _ (Fact.out : radix.Prime).ne_zero⟩
  have hh := output_symbol_nat r B n source dest p q bs qs ns old xs
    (fun j z => payload j (z : ZMod (radix^xs.length))) (fun j z => hwidth j _) i y.val k hi (ZMod.val_lt y) hk
  rw [destination_index,ZMod.natCast_zmod_val,RationalTranslationStream.offset_value r hden] at hh
  exact hh

/-- Other address coordinates remain fixed throughout a represented target fiber. -/
def fiber {ι : Type*} [DecidableEq ι] {Q : ℕ} (address : ι → ZMod Q) (target : ι) (y : ZMod Q) :=
  Function.update address target y

theorem fiber_control {ι : Type*} [DecidableEq ι] {Q : ℕ} (address : ι → ZMod Q)
    (target control : ι) (hne : control ≠ target) (y : ZMod Q) :
    fiber address target y control = address control := Function.update_of_ne hne _ _

/-- On each represented control fiber, the actual output symbol moves to exactly
the target coordinate of OrderedAffine.execute's controlled shift. -/
theorem ordered_affine_symbol {ι : Type*} [LinearOrder ι] (r : ℚ) (hden : r.den < radix) (B n : ℕ)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns old : List Bool) (xs : List (Fin radix))
    (payload : (ι → ZMod (radix^xs.length)) → List (Fin 4))
    (hwidth : ∀ address, (payload address).length = B)
    (addresses : ℕ → ι → ZMod (radix^xs.length)) (target control : ι)
    (hcontrol : ∀ i < n, addresses i control = ((RadixDigits.value xs+i : ℕ) : ZMod (radix^xs.length)))
    (i k : ℕ) (hi : i < n) (hk : k < B) :
    (CountedLoopReuseAlphabet.bank
      (RationalTranslationStream.state r B n source dest p q bs qs old xs
        (fun j z => payload (fiber (addresses j) target (z : ZMod (radix^xs.length)))) n)
      CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1).tape 11
      (q+((i*(radix^xs.length*B)+
        ((OrderedAffine.execute (.shift target control (Swap.Modular.ratMod (radix^xs.length) r)) (addresses i)) target).val*B+k : ℕ) : ℤ)) =
      (RadixToBinary.binaryEncoding (q := radix)).encode ((payload (addresses i))[k]'(by rw [hwidth]; exact hk)) := by
  have hh := output_symbol r hden B n source dest p q bs qs ns old xs
    (fun j z => payload (fiber (addresses j) target z)) (fun j z => hwidth _) i (addresses i target) k hi hk
  simpa only [OrderedAffine.execute,Function.update_self,fiber,Function.update_eq_self,hcontrol i hi] using hh

/-- The concrete machine's time contract includes symbol-by-symbol modular transport. -/
theorem realizes_hoare (r : ℚ) (hden : r.den < radix) {B n : ℕ} (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns old : List Bool) (xs : List (Fin radix))
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^xs.length) (hn : Counter.value ns = n)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cn : GrowingCounterData.Canonical ns) (cold : GrowingCounterData.Canonical old)
    (hold : Counter.value old < radix^xs.length)
    (payload : ℕ → ZMod (radix^xs.length) → List (Fin 4)) (hwidth : ∀ i y, (payload i y).length = B) :
    HoareTime (RationalTranslationStream.program r)
      (fun v => v = CountedLoopReuseAlphabet.bank
        (RationalTranslationStream.state r B n source dest p q bs qs old xs
          (fun j z => payload j (z : ZMod (radix^xs.length))) 0)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1)
      (fun v => v = CountedLoopReuseAlphabet.bank
        (RationalTranslationStream.state r B n source dest p q bs qs old xs
          (fun j z => payload j (z : ZMod (radix^xs.length))) n)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1 ∧
        ∀ (i : ℕ) (y : ZMod (radix^xs.length)) (k : ℕ), i < n → ∀ hk : k < B,
          v.tape 11 (q+((i*(radix^xs.length*B)+
            (y+Swap.Modular.ratMod (radix^xs.length) r*((RadixDigits.value xs+i : ℕ) : ZMod (radix^xs.length))).val*B+k : ℕ) : ℤ)) =
            (RadixToBinary.binaryEncoding (q := radix)).encode ((payload i y)[k]'(by rw [hwidth]; exact hk)))
      (534*(TranslationStream.fibers (radix^xs.length) n
        (fun j z => payload j (z : ZMod (radix^xs.length)))).flatten.length+23) := by
  apply (RationalTranslationStream.translate_hoare_linear r hB source dest p q bs qs ns old xs
    hb hq hn cb cq cn cold hold (fun j z => payload j (z : ZMod (radix^xs.length)))
    (fun j z => hwidth j _)).consequence (fun _ h => h) _ le_rfl
  rintro v rfl
  exact ⟨rfl,fun i y k hi hk => output_symbol r hden B n source dest p q bs qs ns old xs payload hwidth i y k hi hk⟩

section Actual
open Shared50ModularControl (prime)
local instance : Fact prime.Prime := ⟨Shared50ModularControl.prime_prime⟩

/-- Actual network coefficients discharge the only rational-reduction premise
from their proved coefficient origin; no extra denominator hypothesis is needed. -/
theorem actual_ordered_affine_symbol {ι : Type*} [LinearOrder ι] {r : ℚ}
    (hr : Shared50AffineCoefficients.Occurs r) (B n : ℕ)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns old : List Bool) (xs : List (Fin prime))
    (payload : (ι → ZMod (prime^xs.length)) → List (Fin 4))
    (hwidth : ∀ address, (payload address).length = B)
    (addresses : ℕ → ι → ZMod (prime^xs.length)) (target control : ι)
    (hcontrol : ∀ i < n, addresses i control = ((RadixDigits.value xs+i : ℕ) : ZMod (prime^xs.length)))
    (i k : ℕ) (hi : i < n) (hk : k < B) :
    (CountedLoopReuseAlphabet.bank
      (RationalTranslationStream.state r B n source dest p q bs qs old xs
        (fun j z => payload (fiber (addresses j) target (z : ZMod (prime^xs.length)))) n)
      CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1).tape 11
      (q+((i*(prime^xs.length*B)+
        ((OrderedAffine.execute (.shift target control (Swap.Modular.ratMod (prime^xs.length) r)) (addresses i)) target).val*B+k : ℕ) : ℤ)) =
      (RadixToBinary.binaryEncoding (q := prime)).encode ((payload (addresses i))[k]'(by rw [hwidth]; exact hk)) :=
  ordered_affine_symbol r (Shared50AffineCoefficients.denominator_bound hr) B n source dest p q bs qs ns old xs
    payload hwidth addresses target control hcontrol i k hi hk

end Actual

end IntegerMultBounds.Machine.RationalTranslationAffineBridge
