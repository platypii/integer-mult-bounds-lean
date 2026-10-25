module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStageFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrefixRelease

/-! # Release the staged upper rows after the lower call -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.Spec.SignedRingProduct

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

/-- Both product counters are generated on fresh host ports and released. -/
def releaseUpperInput : Pr P 117 Q A U := releaseRows 108 103 94 1 2 111 3 4 5

/-- The original right operand and canonical bank are restored. The caller's
current output, including both product streams, is preserved exactly. -/
theorem releaseUpperInput_with_x_tail_exec {q l w M L : ℕ} (hL : L ≤ 2 ^ l)
    (X V : ℕ → List GaussianInt)
    (v : HS 117 Q A U) (tail resultTail tailX : List (Fin (A + 4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let S := Fixed.startWithTails q l w M L L X (upperOperand q l L X V) tail tailX
      (cstream A w ((List.range M).flatMap V)) inp out
    ∃ v' n, v'.user = v.user ∧
      n ≤ 12 * (M * L * w) + 9 * M + 6 * (L * w) + 9 * L + 18 ∧
      Exec body releaseUpperInput
        (mk v { S with R := Function.update S.R (Fixed.ringReg .out) resultTail }) n
        (mk v' (Fixed.startWithTails q l w M L L X V resultTail tailX [] inp out)) := by
  dsimp only
  let rawV := cstream A w ((List.range M).flatMap V)
  let S := Fixed.startWithTails q l w M L L X (upperOperand q l L X V) tail tailX rawV inp out
  let SU : Stacks 117 A := { S with R := Function.update S.R (Fixed.ringReg .out) resultTail }
  have hrows : (upperRows q l M L X V).length = M * L := by
    exact sliceStream_length M 0 L (by omega) _
  have hsize : (cstream A w (upperRows q l M L X V)).length = M * L * w := by
    simp [hrows]
  obtain ⟨v', n, hu, hn, he⟩ := releaseRows_exec (body := body)
    (batch := 108) (rows := 103) (width := 94) (rowSymbols := 1) (count := 2)
    (src := 111) (saved := 3) (buf := 4) (tmp := 5) (by decide)
    v SU (cstream A w (upperRows q l M L X V)) rawV
    (by simp [SU, S, Fixed.startWithTails, Fixed.start, Fixed.inputBankWithTails,
      Fixed.inputBank, Fixed.ringReg, upperRows_flatMap])
    (by simp [SU, S, Fixed.startWithTails, Fixed.start, Fixed.inputBankWithTails,
      Fixed.inputBank, Fixed.ringReg, hsize, Nat.mul_assoc])
    (by simp [SU, S, Fixed.startWithTails, Fixed.start, Fixed.inputBankWithTails,
      Fixed.inputBank, Fixed.ringReg])
    (by simp [SU, S, Fixed.startWithTails, Fixed.start, Fixed.inputBankWithTails,
      Fixed.inputBank, Fixed.ringReg])
    (by simp [SU, S, Fixed.startWithTails, Fixed.start, Fixed.inputBankWithTails,
      Fixed.inputBank, Fixed.ringReg])
    (by simp [SU, S, Fixed.startWithTails, Fixed.start, Fixed.inputBankWithTails,
      Fixed.inputBank, Fixed.ringReg])
    (by simp [SU, S, Fixed.startWithTails, Fixed.start, Fixed.inputBankWithTails,
      Fixed.inputBank, Fixed.ringReg])
  refine ⟨v', n, hu, ?_, he.cast rfl ?_⟩
  · simpa [SU, S, Fixed.startWithTails, Fixed.start, Fixed.inputBankWithTails,
      Fixed.inputBank, Fixed.ringReg, hsize] using hn
  · apply congrArg (mk v')
    exact staged_input_release_with_x_tail_frame q l w M L X (upperOperand q l L X V) V tail resultTail tailX inp out


theorem releaseUpperInput_exec {q l w M L : ℕ} (hL : L ≤ 2 ^ l)
    (X V : ℕ → List GaussianInt)
    (v : HS 117 Q A U) (tail resultTail : List (Fin (A + 4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let S := Fixed.startWithTails q l w M L L X (upperOperand q l L X V) tail []
      (cstream A w ((List.range M).flatMap V)) inp out
    ∃ v' n, v'.user = v.user ∧
      n ≤ 12 * (M * L * w) + 9 * M + 6 * (L * w) + 9 * L + 18 ∧
      Exec body releaseUpperInput
        (mk v { S with R := Function.update S.R (Fixed.ringReg .out) resultTail }) n
        (mk v' (Fixed.start q l w M L L X V resultTail inp out)) := by
  simpa only [Fixed.startWithTails_nil] using
    releaseUpperInput_with_x_tail_exec hL X V v tail resultTail [] inp out

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
