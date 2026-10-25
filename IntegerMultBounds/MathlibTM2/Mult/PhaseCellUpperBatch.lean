module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUpperInput

/-! # Executed upper Toeplitz batches from unreversed raw operands

Preparation and restoration both execute on S1's existing fixed bank. The result
stream still has padded ring rows; the upper stage reads L-1-i in each row.
Compacting those coefficients into a subsequent stage remains a caller operation.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.ToeplitzInverse

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

/-- Reverse each input row, run the shared convolution, and restore the original input. -/
noncomputable def upperBatch (hQ : rpStates ≤ Q) : Pr P 117 Q A U :=
  .seq reverseInput (.seq (Fixed.program hQ) reverseInput)

/-- One fixed program executes an upper stage with no supplied reversed rows or L*w count. -/
theorem upper_batch_with_x_tail_exec (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    {q l w M L : ℕ} (hq : 1 ≤ q) (hw : q + 2 ≤ w) (hpad : L + L ≤ 2 ^ l + 1)
    (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (v : HS 117 Q A U) (tail tailX : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let S := Fixed.startWithTails q l w M L L X V tail tailX [] inp out
    let SF := { S with R := (Function.update S.R (Fixed.ringReg .out)
      (cstream A w (Fixed.result q l M X (fun j => (V j).reverse)) ++ tail)) }
    ∃ v' n, v'.user = v.user ∧
      n ≤ Fixed.cost q l w M + 2 * (M * (32 * L * w + 19 * L + 17) + 6 * L * w + 9 * L + 20) ∧
      Exec body (upperBatch hQ) (mk v S) n (mk v' SF) ∧
      ∀ j < M, ∀ i < L,
        ‖((2 ^ l : ℕ) : ℂ) * value q (decodeWord
          (((SF.R (Fixed.ringReg .out)).drop ((j * 2 ^ l + (L - 1 - i)) * w)).take w)) -
          upper L (fun k => value q (block (X j) k)) (fun k => value q (block (V j) k)) i‖ ≤
            2 * (2 ^ l : ℕ) / (2 : ℝ) ^ q := by
  dsimp only
  let Y := fun j => (V j).reverse
  let ys := cstream A w (Fixed.result q l M X Y) ++ tail
  have hlenY : ∀ n < M, (Y n).length = L := by simpa only [Y, List.length_reverse] using hlenV
  have hY : ∀ n < M, ∀ z ∈ Y n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q) := by
    intro j hj z hz
    exact hV j hj z (List.mem_reverse.mp hz)
  have hr : 1 ≤ 2 ^ l := Nat.one_le_two_pow
  have hL : L ≤ 2 ^ l := by omega
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := reverseInput_with_x_tail_exec (body := body) q l w M L X V hlenV v tail tailX inp out
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := Fixed.exec_with_tails (body := body) hQ hA hq hw hL hL hpad
    X Y hlenX hlenY hX hY v₁ tail tailX [] inp out
  have he₂' := he₂.cast rfl (congrArg (mk v₂)
    (startWithTails_update_output q l w M L L X Y tail ys tailX [] inp out))
  obtain ⟨v₃, n₃, hu₃, hn₃, he₃⟩ := reverseInput_with_x_tail_exec (body := body) q l w M L X Y hlenY v₂ ys tailX inp out
  have hrestore : (fun j => (Y j).reverse) = V := by funext j; simp [Y]
  rw [hrestore] at he₃
  refine ⟨v₃, n₁ + (n₂ + n₃), hu₃.trans (hu₂.trans hu₁), by omega, ?_, ?_⟩
  · exact (Exec.seq he₁ (Exec.seq he₂' he₃)).cast rfl
      (congrArg (mk v₃) (startWithTails_update_output q l w M L L X V tail ys tailX [] inp out).symm)
  · intro j hj i hi
    simpa only [Function.update_self] using
      upper_output_error hA hw hpad X V hlenX hlenV hX hV tail j hj i hi


theorem upper_batch_exec (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    {q l w M L : ℕ} (hq : 1 ≤ q) (hw : q + 2 ≤ w) (hpad : L + L ≤ 2 ^ l + 1)
    (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (v : HS 117 Q A U) (tail : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let S := Fixed.start q l w M L L X V tail inp out
    let SF := { S with R := (Function.update S.R (Fixed.ringReg .out)
      (cstream A w (Fixed.result q l M X (fun j => (V j).reverse)) ++ tail)) }
    ∃ v' n, v'.user = v.user ∧
      n ≤ Fixed.cost q l w M + 2 * (M * (32 * L * w + 19 * L + 17) + 6 * L * w + 9 * L + 20) ∧
      Exec body (upperBatch hQ) (mk v S) n (mk v' SF) ∧
      ∀ j < M, ∀ i < L,
        ‖((2 ^ l : ℕ) : ℂ) * value q (decodeWord
          (((SF.R (Fixed.ringReg .out)).drop ((j * 2 ^ l + (L - 1 - i)) * w)).take w)) -
          upper L (fun k => value q (block (X j) k)) (fun k => value q (block (V j) k)) i‖ ≤
            2 * (2 ^ l : ℕ) / (2 : ℝ) ^ q := by
  simpa only [Fixed.startWithTails_nil] using
    upper_batch_with_x_tail_exec hQ hA hq hw hpad X V hlenX hlenV hX hV
      v tail [] inp out

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
