import IntegerMultBounds.Machine.ButterflyNumerator
import IntegerMultBounds.Networks.GaussianDyadic

/-! Signed interpretation and exact dyadic semantics for the physical butterfly
numerator machine. Advancing the common denominator by one implements division
by two exactly; a guard bound makes centered residue decoding unambiguous. -/
namespace IntegerMultBounds.Machine.ButterflySigned
noncomputable section
open ButterflyNumerator

/-- A word of `b+1` bits represents the centered integer in `[-2^b,2^b)`. -/
def signedValue (b : ℕ) (xs : List (Fin 2)) : ℤ :=
  if RadixDigits.value xs < 2^b then (RadixDigits.value xs : ℤ)
  else (RadixDigits.value xs : ℤ)-(2^(b+1) : ℕ)

theorem signed_bounds (b : ℕ) (xs : List (Fin 2)) (hw : xs.length=b+1) :
    -(2^b : ℕ) ≤ signedValue b xs ∧ signedValue b xs < (2^b : ℕ) := by
  have hv := RadixDigits.value_lt (by decide : 2 ≤ 2) xs
  rw [hw] at hv
  have hp : 2^(b+1)=2*2^b := by rw [pow_succ]; omega
  unfold signedValue
  split_ifs with h
  · exact ⟨by omega,by exact_mod_cast h⟩
  · rw [hp] at hv ⊢
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    omega

theorem signed_cast (b : ℕ) (xs : List (Fin 2)) :
    (signedValue b xs : ZMod (2^(b+1)))=(RadixDigits.value xs : ZMod (2^(b+1))) := by
  unfold signedValue
  split_ifs
  · simp only [Int.cast_natCast]
  · rw [Int.cast_sub,Int.cast_natCast,Int.cast_natCast,ZMod.natCast_self,sub_zero]

/-- Equality of residues plus the signed guard interval implies literal integer
correctness; this is not an assumed arithmetic specification. -/
theorem signed_unique (b : ℕ) (xs : List (Fin 2)) (hw : xs.length=b+1)
    (x : ℤ) (hx : -(2^b : ℕ) ≤ x ∧ x < (2^b : ℕ))
    (he : (RadixDigits.value xs : ZMod (2^(b+1)))=(x : ZMod (2^(b+1)))) :
    signedValue b xs=x := by
  have hs := signed_bounds b xs hw
  have hp : (2^(b+1) : ℕ)=2*2^b := by rw [pow_succ]; omega
  have hmod : ((signedValue b xs+(2^b : ℕ) : ℤ) : ZMod (2^(b+1)))=
      ((x+(2^b : ℕ) : ℤ) : ZMod (2^(b+1))) := by
    push_cast
    rw [signed_cast,he]
  rw [ZMod.intCast_eq_intCast_iff'] at hmod
  have hsl : 0 ≤ signedValue b xs+(2^b : ℕ) := by omega
  have hsu : signedValue b xs+(2^b : ℕ) < (2^(b+1) : ℕ) := by rw [hp]; simp only [Nat.cast_mul,Nat.cast_ofNat]; omega
  have hxl : 0 ≤ x+(2^b : ℕ) := by omega
  have hxu : x+(2^b : ℕ) < (2^(b+1) : ℕ) := by rw [hp]; simp only [Nat.cast_mul,Nat.cast_ofNat]; omega
  rw [Int.emod_eq_of_lt hsl hsu,Int.emod_eq_of_lt hxl hxu] at hmod
  omega

theorem numerator_bound (x : Fin 4 → ℤ) (M : ℤ) (hx : ∀ j,|x j| ≤ M) (i : Fin 4) :
    |numerator x i| ≤ 4*M := by
  have h0 := (abs_le.mp (hx 0)); have h1 := (abs_le.mp (hx 1))
  have h2 := (abs_le.mp (hx 2)); have h3 := (abs_le.mp (hx 3))
  fin_cases i <;> simp [numerator,abs_le] <;> constructor <;> linarith

/-- Four bounded signed inputs yield the actual integer numerators, not merely
congruent residues. The two-sided coefficient guard is explicit. -/
theorem words_signed (xs : ℕ → List (Fin 2)) (b : ℕ) (hw : ∀ j,(xs j).length=b+1)
    (x : Fin 4 → ℤ) (hx : ∀ j : Fin 4,(RadixDigits.value (xs j.val) : ZMod (2^(b+1)))=(x j : ZMod (2^(b+1))))
    (M : ℤ) (hM : ∀ j,|x j| ≤ M) (hguard : 4*M < (2^b : ℕ)) (i : Fin 4) :
    signedValue b (words i xs)=numerator x i := by
  apply signed_unique b (words i xs) (words_length i xs (b+1) hw) (numerator x i)
  · have hb := abs_le.mp (numerator_bound x M hM i)
    constructor <;> omega
  · exact words_integer xs (b+1) hw x hx i

/-- Exact common-denominator encoding of a Gaussian dyadic coefficient. -/
def complexValue (a b : ℤ) (n : ℕ) : ℂ := ((a : ℂ)+(b : ℂ)*Complex.I)/(2:ℂ)^n

/-- The first output pair represents the plus branch of the actual manuscript
butterfly at one additional binary precision place. -/
theorem complex_first (x : Fin 4 → ℤ) (n : ℕ) :
    complexValue (numerator x 0) (numerator x 1) (n+1)=
      (complexValue (x 0) (x 1) n+complexValue (x 2) (x 3) n+
        Complex.I*(complexValue (x 0) (x 1) n-complexValue (x 2) (x 3) n))/2 := by
  simp [complexValue,numerator,pow_succ]
  field_simp
  linear_combination -((x 1 : ℂ)-(x 3 : ℂ))*Complex.I_sq

/-- The second output pair represents the minus branch at that same precision. -/
theorem complex_second (x : Fin 4 → ℤ) (n : ℕ) :
    complexValue (numerator x 2) (numerator x 3) (n+1)=
      (complexValue (x 0) (x 1) n+complexValue (x 2) (x 3) n-
        Complex.I*(complexValue (x 0) (x 1) n-complexValue (x 2) (x 3) n))/2 := by
  simp [complexValue,numerator,pow_succ]
  field_simp
  linear_combination ((x 1 : ℂ)-(x 3 : ℂ))*Complex.I_sq

/-- The decoded inputs themselves determine the exact output butterfly. No
external correctness hypothesis about a signed codec is required. -/
theorem words_butterfly (xs : ℕ → List (Fin 2)) (b n : ℕ)
    (hw : ∀ j,(xs j).length=b+1) (M : ℤ)
    (hM : ∀ j : Fin 4,|signedValue b (xs j.val)| ≤ M) (hguard : 4*M < (2^b : ℕ)) :
    let x : Fin 4 → ℤ := fun j => signedValue b (xs j.val)
    let y : Fin 4 → ℤ := fun j => signedValue b (words j xs)
    let u := complexValue (x 0) (x 1) n
    let v := complexValue (x 2) (x 3) n
    complexValue (y 0) (y 1) (n+1)=(u+v+Complex.I*(u-v))/2 ∧
    complexValue (y 2) (y 3) (n+1)=(u+v-Complex.I*(u-v))/2 := by
  dsimp only
  have h (i : Fin 4) : signedValue b (words i xs)=
      numerator (fun j : Fin 4 => signedValue b (xs j.val)) i :=
    words_signed xs b hw _ (fun j => (signed_cast b (xs j.val)).symm) M hM hguard i
  rw [h 0,h 1,h 2,h 3]
  exact ⟨complex_first _ n,complex_second _ n⟩

/-- Complete timed arithmetic kernel: the actual output bank is preserved in the
postcondition together with the exact complex butterfly meaning of its words. -/
theorem runs_exact (xs : ℕ → List (Fin 2)) (b n : ℕ)
    (hw : ∀ j,(xs j).length=b+1) (M : ℤ)
    (hM : ∀ j : Fin 4,|signedValue b (xs j.val)| ≤ M) (hguard : 4*M < (2^b : ℕ)) :
    let x : Fin 4 → ℤ := fun j => signedValue b (xs j.val)
    let y : Fin 4 → ℤ := fun j => signedValue b (words j xs)
    let u := complexValue (x 0) (x 1) n
    let v := complexValue (x 2) (x 3) n
    HoareTime ButterflyNumerator.program (fun tapes => tapes=ButterflyNumerator.input xs)
      (fun tapes => tapes=ButterflyNumerator.output xs ∧
        complexValue (y 0) (y 1) (n+1)=(u+v+Complex.I*(u-v))/2 ∧
        complexValue (y 2) (y 3) (n+1)=(u+v-Complex.I*(u-v))/2)
      (168*(b+1)+591) := by
  apply (ButterflyNumerator.runs xs (b+1) hw).consequence (fun _ h => h) _ le_rfl
  intro tapes ht
  exact ⟨ht,words_butterfly xs b n hw M hM hguard⟩

end
end IntegerMultBounds.Machine.ButterflySigned
