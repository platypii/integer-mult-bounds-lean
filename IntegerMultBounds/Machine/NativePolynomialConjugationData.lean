import IntegerMultBounds.Machine.ButterflyStreamSemantics
import IntegerMultBounds.Machine.TwosComplement

/-! Exact native two's-complement conjugation. Real fields stay literal,
imaginary fields are modularly negated at unchanged width. A strict signed
guard rules out the unrepresentable negation of the most-negative word. -/
namespace IntegerMultBounds.Machine.NativePolynomialConjugationData
noncomputable section
open ButterflyStreamData (Coefficient)

def digit (b : Bool) : Fin 2 := if b then 1 else 0
def bits (xs : List (Fin 2)) := xs.map (fun x => decide (x=1))
def digits (bs : List Bool) := bs.map digit

theorem digits_bits (xs : List (Fin 2)) : digits (bits xs)=xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => fin_cases x <;> simp [digits,bits,digit] at * <;> exact ih

theorem bits_digits (bs : List Bool) : bits (digits bs)=bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [bits,digits,digit] at * <;> exact ih

def negative (xs : List (Fin 2)) := digits (TwosComplement.negWord (bits xs))
def coefficient (x : Coefficient) : Coefficient := (x.1,negative x.2)
def array {N : ℕ} (f : Fin N → Coefficient) := fun i => coefficient (f i)

theorem negative_length (xs : List (Fin 2)) : (negative xs).length=xs.length := by
  simp [negative,digits,bits,TwosComplement.negWord_length]
theorem coefficient_width (x : Coefficient) :
    (coefficient x).1.length=x.1.length ∧ (coefficient x).2.length=x.2.length :=
  ⟨rfl,negative_length x.2⟩

theorem bits_value (xs : List (Fin 2)) : Counter.value (bits xs)=RadixDigits.value xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => fin_cases x <;> simp [bits,Counter.value,RadixDigits.value] at * <;> omega

/-- The existing centered signed codec agrees with the proved Boolean
 two's-complement interpretation at every positive retained width. -/
theorem signed_decode (b : ℕ) (xs : List (Fin 2)) (hw : xs.length=b+1) :
    ButterflySigned.signedValue b xs=TwosComplement.signed (bits xs) := by
  have hn : bits xs≠[] := by intro h; have hh := congrArg List.length h; simp [bits,hw] at hh
  have hs := TwosComplement.signed_bounds (bits xs) hn
  have hl : (bits xs).length-1=b := by simp [bits,hw]
  rw [hl] at hs
  apply ButterflySigned.signed_unique b xs hw _
  · constructor
    · exact_mod_cast hs.1
    · exact_mod_cast hs.2
  · unfold TwosComplement.signed
    rw [bits_value]
    simp only [bits,List.length_map,hw]
    have hz : (2 : ZMod (2^(b+1)))^(b+1)=0 := by
      change ((2 : ℕ) : ZMod (2^(b+1)))^(b+1)=0
      rw [←Nat.cast_pow]
      exact ZMod.natCast_self _
    split_ifs <;> simp [Int.cast_sub,hz]

theorem negative_signed (b : ℕ) (xs : List (Fin 2)) (hw : xs.length=b+1)
    (hguard : |ButterflySigned.signedValue b xs|<(2^b : ℕ)) :
    ButterflySigned.signedValue b (negative xs) = -ButterflySigned.signedValue b xs := by
  rw [signed_decode b _ ((negative_length xs).trans hw),negative,bits_digits,
    signed_decode b xs hw]
  apply TwosComplement.signed_negWord
  · intro h
    have hh := congrArg List.length h
    simp [bits,hw] at hh
  · have hg := (abs_lt.mp hguard).1
    rw [signed_decode b xs hw] at hg
    have hl : (bits xs).length-1=b := by simp [bits,hw]
    rw [hl]
    exact ne_of_gt (by exact_mod_cast hg)

theorem complex_conjugate (a b : ℤ) (n : ℕ) :
    ButterflySigned.complexValue a (-b) n=star (ButterflySigned.complexValue a b n) := by
  simp [ButterflySigned.complexValue]

theorem decoded (half precision : ℕ) (x : Coefficient)
    (hw : x.2.length=half+1)
    (hguard : |ButterflySigned.signedValue half x.2|<(2^half : ℕ)) :
    ButterflyStreamSemantics.decode half precision (coefficient x)=
      star (ButterflyStreamSemantics.decode half precision x) := by
  unfold ButterflyStreamSemantics.decode coefficient
  rw [negative_signed half x.2 hw hguard]
  exact complex_conjugate _ _ _

end
end IntegerMultBounds.Machine.NativePolynomialConjugationData
