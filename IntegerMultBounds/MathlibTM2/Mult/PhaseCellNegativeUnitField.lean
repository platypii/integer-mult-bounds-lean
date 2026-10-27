module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNegativeUnitBasis
public import IntegerMultBounds.MathlibTM2.Mult.ChirpCyclicMath
public import IntegerMultBounds.NLogN.SchurBlockSolve

/-! The generated negative basis stream supplies an exact unit source for matrix columns. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open scoped BigOperators
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN

def negativeUnitField {s : ℕ} (q : ℕ) (j i : ZMod s) : GaussianInt :=
  if i = j then ⟨-(2 : ℤ)^q,0⟩ else 0

theorem negativeUnitField_value {s : ℕ} (q : ℕ) (j i : ZMod s) :
    value q (negativeUnitField q j i) = if i = j then (-1 : ℂ) else 0 := by
  by_cases h : i = j <;>
    simp [negativeUnitField,h,value,Complex.ext_iff,show (2 : ℝ)^q ≠ 0 by positivity]

theorem negativeUnitField_norm {s : ℕ} (q : ℕ) (j i : ZMod s) :
    ‖value q (negativeUnitField q j i)‖ ≤ 1 := by
  rw [negativeUnitField_value]
  split_ifs <;> simp

@[simp] theorem negativeUnitField_real {s : ℕ} (q : ℕ) (j i : ZMod s) :
    (negativeUnitField q j i).im = 0 := by
  by_cases h : i = j <;> simp [negativeUnitField,h]

theorem negativeUnitField_words {s : ℕ} [NeZero s] (q : ℕ) (j : ZMod s) :
    chirpLine s (negativeUnitField q j) = negativeUnitWords q s j.val := by
  apply List.ext_getElem (by simp [negativeUnitWords]; have := j.val_lt; omega)
  intro i hi hi'
  have hiS : i < s := by simpa only [length_chirpLine] using hi
  have he : (i : ZMod s) = j ↔ i = j.val := by
    constructor
    · intro hh
      simpa only [ZMod.val_cast_of_lt hiS] using congrArg ZMod.val hh
    · intro hh
      apply ZMod.val_injective
      simpa only [ZMod.val_cast_of_lt hiS] using hh
  by_cases hlt : i < j.val
  · have hne : i ≠ j.val := by omega
    simp [chirpLine,negativeUnitField,he,hne,negativeUnitWords,List.getElem_append,hlt]
  · by_cases heq : i = j.val
    · subst i
      simp [chirpLine,negativeUnitField,negativeUnitWords,List.getElem_append]
    · have hgt : j.val < i := by omega
      obtain ⟨d,hshift⟩ : ∃ d, i-j.val = d+1 := ⟨i-j.val-1,by omega⟩
      simp [chirpLine,negativeUnitField,he,heq,negativeUnitWords,List.getElem_append,hlt,hshift]

/-- Boundary coupling against the exact negative unit is minus the original column. -/
theorem couple_negative_unit {s : ℕ} (A : Matrix (ZMod s) (ZMod s) ℝ) (B : Finset (ZMod s))
    (q : ℕ) (j : ZMod s) (hj : j ∈ B) (i : ZMod s) :
    -SchurDominance.couple A B (fun k => (value q (negativeUnitField q j k)).re) i = A i j := by
  have hval (k : ZMod s) : (value q (negativeUnitField q j k)).re = if k = j then (-1 : ℝ) else 0 := by
    rw [negativeUnitField_value]
    split_ifs <;> rfl
  simp [SchurDominance.couple,hval,hj]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
