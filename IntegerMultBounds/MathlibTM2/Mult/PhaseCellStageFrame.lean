module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUpperOperand

/-! # Exact bank frame between the upper and lower triangular products -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.Spec.SignedRingProduct

/-- Compaction onto the raw right operand retains its original stream below the
new rows. The padded upper result becomes the next product's output suffix. -/
theorem upper_crop_stage_with_x_tail_frame {A : ℕ} (q l w M L : ℕ)
    (X V : ℕ → List GaussianInt) (tail tailX : List (Fin (A + 4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let S := Fixed.startWithTails q l w M L L X V tail tailX [] inp out
    let ys := cstream A w (Fixed.result q l M X (fun n => (V n).reverse)) ++ tail
    { S with R := (Function.update (Function.update S.R (Fixed.ringReg .out) ys)
      111 (cstream A w (upperRows q l M L X V) ++ S.R 111)) } =
    Fixed.startWithTails q l w M L L X (upperOperand q l L X V) ys tailX
      (cstream A w ((List.range M).flatMap V)) inp out := by
  dsimp only
  rw [upperRows_flatMap]
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  by_cases hx : k.val = 110
  · have hk : k = (110 : Fin 117) := Fin.ext hx
    subst k
    simp [Fixed.startWithTails, Fixed.start, Fixed.inputBankWithTails,
      Fixed.inputBank, Fixed.ringReg]
  · by_cases hy : k.val = 111
    · have hk : k = (111 : Fin 117) := Fin.ext hy
      subst k
      simp [Fixed.startWithTails, Fixed.start, Fixed.inputBankWithTails,
        Fixed.inputBank, Fixed.ringReg]
    · by_cases ho : k.val = 93
      · have hk : k = (93 : Fin 117) := Fin.ext ho
        subst k
        simp [Fixed.startWithTails, Fixed.start, Fixed.inputBankWithTails,
          Fixed.inputBank, Fixed.ringReg]
      · have h111 : k ≠ (111 : Fin 117) := fun h => hy (congrArg Fin.val h)
        have h93 : k ≠ (93 : Fin 117) := fun h => ho (congrArg Fin.val h)
        simp [Fixed.startWithTails, Fixed.start, Fixed.inputBankWithTails,
          Fixed.inputBank, Fixed.ringReg, hx, hy, ho, h111, h93]

theorem upper_crop_stage_frame {A : ℕ} (q l w M L : ℕ)
    (X V : ℕ → List GaussianInt) (tail : List (Fin (A + 4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let S := Fixed.start q l w M L L X V tail inp out
    let ys := cstream A w (Fixed.result q l M X (fun n => (V n).reverse)) ++ tail
    { S with R := (Function.update (Function.update S.R (Fixed.ringReg .out) ys)
      111 (cstream A w (upperRows q l M L X V) ++ S.R 111)) } =
    Fixed.startWithTails q l w M L L X (upperOperand q l L X V) ys []
      (cstream A w ((List.range M).flatMap V)) inp out := by
  simpa only [Fixed.startWithTails_nil] using
    upper_crop_stage_with_x_tail_frame q l w M L X V tail [] inp out

/-- Removing a staged operand prefix restores the original canonical bank,
while retaining any result prefix already published on the output stack. -/
theorem staged_input_release_with_x_tail_frame {A : ℕ} (q l w M L : ℕ)
    (X Y V : ℕ → List GaussianInt) (tail resultTail tailX : List (Fin (A + 4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let rawV := cstream A w ((List.range M).flatMap V)
    let S := Fixed.startWithTails q l w M L L X Y tail tailX rawV inp out
    { S with R := (Function.update (Function.update S.R (Fixed.ringReg .out) resultTail)
      111 rawV) } = Fixed.startWithTails q l w M L L X V resultTail tailX [] inp out := by
  dsimp only
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  by_cases hx : k.val = 110
  · have hk : k = (110 : Fin 117) := Fin.ext hx
    subst k
    simp [Fixed.startWithTails, Fixed.start, Fixed.inputBankWithTails,
      Fixed.inputBank, Fixed.ringReg]
  · by_cases hy : k.val = 111
    · have hk : k = (111 : Fin 117) := Fin.ext hy
      subst k
      simp [Fixed.startWithTails, Fixed.start, Fixed.inputBankWithTails,
        Fixed.inputBank, Fixed.ringReg]
    · by_cases ho : k.val = 93
      · have hk : k = (93 : Fin 117) := Fin.ext ho
        subst k
        simp [Fixed.startWithTails, Fixed.start, Fixed.inputBankWithTails,
          Fixed.inputBank, Fixed.ringReg]
      · have h111 : k ≠ (111 : Fin 117) := fun h => hy (congrArg Fin.val h)
        have h93 : k ≠ (93 : Fin 117) := fun h => ho (congrArg Fin.val h)
        simp [Fixed.startWithTails, Fixed.start, Fixed.inputBankWithTails,
          Fixed.inputBank, Fixed.ringReg, hx, hy, ho, h111, h93]


theorem staged_input_release_frame {A : ℕ} (q l w M L : ℕ)
    (X Y V : ℕ → List GaussianInt) (tail resultTail : List (Fin (A + 4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let rawV := cstream A w ((List.range M).flatMap V)
    let S := Fixed.startWithTails q l w M L L X Y tail [] rawV inp out
    { S with R := (Function.update (Function.update S.R (Fixed.ringReg .out) resultTail)
      111 rawV) } = Fixed.start q l w M L L X V resultTail inp out := by
  simpa only [Fixed.startWithTails_nil] using
    staged_input_release_with_x_tail_frame q l w M L X Y V tail resultTail [] inp out

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
