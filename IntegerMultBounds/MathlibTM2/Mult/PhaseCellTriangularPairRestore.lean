module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTriangularPair
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputRelease

/-! # Restore raw operands after the executed triangular pair

Intermediate numerators remain normalized q-grid words. The interpretation keeps
the ring scaling explicit. Temporary intermediate streams are retained in the
postcondition; their later release is not assumed or included for free.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.Spec.SignedRingProduct IntegerMultBounds.NLogN.ToeplitzInverse

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

/-- Release the compact intermediate after both products have executed. -/
noncomputable def triangularPairRestored (hQ : rpStates ≤ Q) : Pr P 117 Q A U :=
  .seq (triangularPair hQ) releaseUpperInput

/-- The canonical raw-input bank is restored, including the original right operand.
Both padded product streams remain as a charged output prefix for later extraction. -/
theorem triangularPairRestored_with_x_tail_exec (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    {q l w M L : ℕ} (hq : 1 ≤ q) (hw : q + 2 ≤ w) (hpad : L + L ≤ 2 ^ l + 1)
    (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (v : HS 117 Q A U) (tail tailX : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let ys := cstream A w (Fixed.result q l M X (fun n => (V n).reverse)) ++ tail
    let SF := Fixed.startWithTails q l w M L L X V
      (cstream A w (Fixed.result q l M X (upperOperand q l L X V)) ++ ys) tailX [] inp out
    ∃ v' n, v'.user = v.user ∧
      n ≤ 2 * Fixed.cost q l w M +
        2 * (M * (32 * L * w + 19 * L + 17) + 6 * L * w + 9 * L + 20) +
        (M * (20 * L * w + 19 * L + 6 * 2 ^ l * w + 23) +
          4 * w + 6 * 2 ^ l * w + 9 * l + 22) +
        (12 * (M * L * w) + 9 * M + 6 * (L * w) + 9 * L + 18) ∧
      Exec body (triangularPairRestored hQ) (mk v (Fixed.startWithTails q l w M L L X V tail tailX [] inp out)) n
        (mk v' SF) ∧
      ∀ j < M, ∀ i < L,
        ‖((2 ^ l : ℕ) : ℂ) * value q (decodeWord
          (((SF.R (Fixed.ringReg .out)).drop ((j * 2 ^ l + i) * w)).take w)) -
          lower (fun k => value q (block (X j) k))
            (fun k => value q (block (upperOperand q l L X V j) k)) i‖ ≤
          2 * (2 ^ l : ℕ) / (2 : ℝ) ^ q := by
  dsimp only
  have hr : 1 ≤ 2 ^ l := Nat.one_le_two_pow
  have hL : L ≤ 2 ^ l := by omega
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁, herr⟩ := triangularPair_with_x_tail_exec (body := body)
    hQ hA hq hw hpad X V hlenX hlenV hX hV v tail tailX inp out
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := releaseUpperInput_with_x_tail_exec (body := body) hL X V v₁
    (cstream A w (Fixed.result q l M X (fun n => (V n).reverse)) ++ tail)
    (cstream A w (Fixed.result q l M X (upperOperand q l L X V)) ++
      (cstream A w (Fixed.result q l M X (fun n => (V n).reverse)) ++ tail)) tailX inp out
  refine ⟨v₂, n₁ + n₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂, ?_⟩
  intro j hj i hi
  simpa [Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank, Fixed.ringReg] using herr j hj i hi


theorem triangularPairRestored_exec (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    {q l w M L : ℕ} (hq : 1 ≤ q) (hw : q + 2 ≤ w) (hpad : L + L ≤ 2 ^ l + 1)
    (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (v : HS 117 Q A U) (tail : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let ys := cstream A w (Fixed.result q l M X (fun n => (V n).reverse)) ++ tail
    let SF := Fixed.start q l w M L L X V
      (cstream A w (Fixed.result q l M X (upperOperand q l L X V)) ++ ys) inp out
    ∃ v' n, v'.user = v.user ∧
      n ≤ 2 * Fixed.cost q l w M +
        2 * (M * (32 * L * w + 19 * L + 17) + 6 * L * w + 9 * L + 20) +
        (M * (20 * L * w + 19 * L + 6 * 2 ^ l * w + 23) +
          4 * w + 6 * 2 ^ l * w + 9 * l + 22) +
        (12 * (M * L * w) + 9 * M + 6 * (L * w) + 9 * L + 18) ∧
      Exec body (triangularPairRestored hQ) (mk v (Fixed.start q l w M L L X V tail inp out)) n
        (mk v' SF) ∧
      ∀ j < M, ∀ i < L,
        ‖((2 ^ l : ℕ) : ℂ) * value q (decodeWord
          (((SF.R (Fixed.ringReg .out)).drop ((j * 2 ^ l + i) * w)).take w)) -
          lower (fun k => value q (block (X j) k))
            (fun k => value q (block (upperOperand q l L X V j) k)) i‖ ≤
          2 * (2 ^ l : ℕ) / (2 : ℝ) ^ q := by
  simpa only [Fixed.startWithTails_nil] using
    triangularPairRestored_with_x_tail_exec hQ hA hq hw hpad X V hlenX hlenV hX hV
      v tail [] inp out

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
