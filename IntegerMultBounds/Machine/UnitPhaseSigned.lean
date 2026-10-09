import IntegerMultBounds.Machine.UnitPhaseNumerator
import IntegerMultBounds.Machine.ButterflySigned

/-! Exact centered signed and Gaussian dyadic semantics of the physical unit
phase multiplier. A strict guard excludes the unrepresentable negation of the
most negative word; numerator width and denominator precision are retained. -/
namespace IntegerMultBounds.Machine.UnitPhaseSigned
noncomputable section
open UnitPhaseNumerator
open ButterflySigned (signedValue signed_cast signed_unique complexValue)

theorem numerator_abs (p : Fin 4) (x : Fin 2 → ℤ) (i : Fin 2) : |numerator p x i|=|x (source p i)| := by
  unfold numerator
  split_ifs <;> simp

theorem words_signed (p : Fin 4) (i : Fin 2) (xs : ℕ → List (Fin 2)) (b : ℕ)
    (hw : ∀ j,(xs j).length=b+1) (x : Fin 2 → ℤ)
    (hx : ∀ j,(RadixDigits.value (xs j.val) : ZMod (2^(b+1)))=(x j : ZMod (2^(b+1))))
    (hguard : ∀ j,|x j|<(2^b : ℕ)) : signedValue b (words p i xs)=numerator p x i := by
  apply signed_unique b _ (words_length p i xs (b+1) hw) _
  · have ha : |numerator p x i|<(2^b : ℕ) := by rw [numerator_abs]; exact hguard _
    have hb := abs_lt.mp ha
    exact ⟨hb.1.le,hb.2⟩
  · rw [words_value p i xs (b+1) hw]
    have he : (fun j : Fin 2 => (RadixDigits.value (xs j.val) : ZMod (2^(b+1))))=
        fun j => (x j : ZMod (2^(b+1))) := funext hx
    rw [he]
    unfold numerator
    split_ifs <;> simp

theorem numerator_complex (p : Fin 4) (x : Fin 2 → ℤ) :
    ((numerator p x 0 : ℤ) : ℂ)+((numerator p x 1 : ℤ) : ℂ)*Complex.I=
      Networks.BinaryPhase.phase (p.val : ZMod 4)*((x 0 : ℂ)+(x 1 : ℂ)*Complex.I) := by
  fin_cases p
  · change (x 0 : ℂ)+(x 1 : ℂ)*Complex.I=Complex.I^0*((x 0 : ℂ)+(x 1 : ℂ)*Complex.I)
    simp
  · change ((-x 1 : ℤ) : ℂ)+(x 0 : ℂ)*Complex.I=Complex.I^1*((x 0 : ℂ)+(x 1 : ℂ)*Complex.I)
    push_cast
    simp only [pow_one]
    linear_combination -((x 1 : ℂ))*Complex.I_sq
  · change ((-x 0 : ℤ) : ℂ)+((-x 1 : ℤ) : ℂ)*Complex.I=Complex.I^2*((x 0 : ℂ)+(x 1 : ℂ)*Complex.I)
    push_cast
    rw [Complex.I_sq]
    ring
  · change (x 1 : ℂ)+((-x 0 : ℤ) : ℂ)*Complex.I=Complex.I^3*((x 0 : ℂ)+(x 1 : ℂ)*Complex.I)
    push_cast
    rw [show Complex.I^3 = -Complex.I by norm_num [pow_succ,Complex.I_sq]]
    linear_combination (x 1 : ℂ)*Complex.I_sq

theorem complex_phase (p : Fin 4) (x : Fin 2 → ℤ) (n : ℕ) :
    complexValue (numerator p x 0) (numerator p x 1) n=
      Networks.BinaryPhase.phase (p.val : ZMod 4)*complexValue (x 0) (x 1) n := by
  unfold complexValue
  rw [numerator_complex,mul_div_assoc]

theorem words_phase (p : Fin 4) (xs : ℕ → List (Fin 2)) (b n : ℕ)
    (hw : ∀ j,(xs j).length=b+1) (hguard : ∀ j : Fin 2,|signedValue b (xs j.val)|<(2^b : ℕ)) :
    complexValue (signedValue b (words p 0 xs)) (signedValue b (words p 1 xs)) n=
      Networks.BinaryPhase.phase (p.val : ZMod 4)*complexValue (signedValue b (xs 0)) (signedValue b (xs 1)) n := by
  have h (i : Fin 2) := words_signed p i xs b hw (fun j => signedValue b (xs j.val))
    (fun j => (signed_cast b (xs j.val)).symm) hguard
  rw [h 0,h 1]
  exact complex_phase p _ n

end
end IntegerMultBounds.Machine.UnitPhaseSigned
