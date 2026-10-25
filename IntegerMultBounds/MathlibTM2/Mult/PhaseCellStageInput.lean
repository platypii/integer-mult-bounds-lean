module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStageFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUpperCropSetup

/-! # Executed staging of compact upper rows for the lower product -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.Spec.SignedRingProduct

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

/-- Reuse empty host work ports and the retained unary dimensions. -/
def upperToLowerInput : Pr P 117 Q A U :=
  upperCropFromDimensions 101 108 1 2 3 103 4 94 5 93 6 7 8 9 10 11 111

/-- Staging executes, generates its counter and restores every work port. The original
right operand remains beneath the new rows; no second operand stream is supplied. -/
theorem upperToLowerInput_with_x_tail_exec {q l w M L : ℕ}
    (hA : 4 ≤ A) (hw : q + 2 ≤ w) (hpad : L + L ≤ 2 ^ l + 1)
    (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (v : HS 117 Q A U) (tail tailX : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let S := Fixed.startWithTails q l w M L L X V tail tailX [] inp out
    let ys := cstream A w (Fixed.result q l M X (fun n => (V n).reverse)) ++ tail
    ∃ v' n, v'.user = v.user ∧
      n ≤ M * (20 * L * w + 19 * L + 6 * 2 ^ l * w + 23) +
        4 * w + 6 * 2 ^ l * w + 9 * l + 22 ∧
      Exec body upperToLowerInput
        (mk v { S with R := Function.update S.R (Fixed.ringReg .out) ys }) n
        (mk v' (Fixed.startWithTails q l w M L L X (upperOperand q l L X V) ys tailX
          (cstream A w ((List.range M).flatMap V)) inp out)) := by
  dsimp only
  let S := Fixed.startWithTails q l w M L L X V tail tailX [] inp out
  let ys := cstream A w (Fixed.result q l M X (fun n => (V n).reverse)) ++ tail
  let SU : Stacks 117 A := { S with R := Function.update S.R (Fixed.ringReg .out) ys }
  obtain ⟨v', n, hu, hn, he, _⟩ := upperCropFromDimensions_exec (body := body)
    (lR := 101) (dst := 111) (batch := 108) (batchSaved := 1) (skip := 2)
    (savedSkip := 3) (mR := 103) (recordSaved := 4) (wordR := 94) (recordSymbols := 5)
    (src := 93) (acc := 6) (current := 7) (savedSource := 8) (saved := 9) (buf := 10) (tmp := 11)
    (by decide) hA hw hpad X V hlenX hlenV hX hV v SU tail
    (by simp [SU, S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank, Fixed.ringReg])
    (by simp [SU, S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank, Fixed.ringReg])
    (by simp [SU, ys, Fixed.ringReg])
    (by simp [SU, S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank, Fixed.ringReg])
    (by simp [SU, S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank, Fixed.ringReg])
    (by simp [SU, S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank, Fixed.ringReg])
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [SU, S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank, Fixed.ringReg])
  refine ⟨v', n, hu, hn, he.cast rfl ?_⟩
  apply congrArg (mk v')
  simpa only [SU, S, Function.update_of_ne (show (111 : Fin 117) ≠ Fixed.ringReg .out by decide)] using
    upper_crop_stage_with_x_tail_frame q l w M L X V tail tailX inp out


theorem upperToLowerInput_exec {q l w M L : ℕ}
    (hA : 4 ≤ A) (hw : q + 2 ≤ w) (hpad : L + L ≤ 2 ^ l + 1)
    (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (v : HS 117 Q A U) (tail : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let S := Fixed.start q l w M L L X V tail inp out
    let ys := cstream A w (Fixed.result q l M X (fun n => (V n).reverse)) ++ tail
    ∃ v' n, v'.user = v.user ∧
      n ≤ M * (20 * L * w + 19 * L + 6 * 2 ^ l * w + 23) +
        4 * w + 6 * 2 ^ l * w + 9 * l + 22 ∧
      Exec body upperToLowerInput
        (mk v { S with R := Function.update S.R (Fixed.ringReg .out) ys }) n
        (mk v' (Fixed.startWithTails q l w M L L X (upperOperand q l L X V) ys []
          (cstream A w ((List.range M).flatMap V)) inp out)) := by
  simpa only [Fixed.startWithTails_nil] using
    upperToLowerInput_with_x_tail_exec hA hw hpad X V hlenX hlenV hX hV
      v tail [] inp out

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
