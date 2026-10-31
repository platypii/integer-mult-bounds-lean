module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLowerBatch
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvFixedStock

/-! Lower triangular interpretation on the certified fixed convolution trace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.ToeplitzInverse
variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

theorem lower_batch_with_tails_exec_within (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    {q l w M L : ℕ} (hq : 1 ≤ q) (hw : q + 2 ≤ w) (hpad : L + L ≤ 2 ^ l + 1)
    (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (v : HS 117 Q A U) (tail tailX tailV : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (C : ℕ) (hpush : mnProgPush (rpProg (P := P) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hQ) ≤ C) (depth : ℕ) :
    let S := Fixed.startWithTails q l w M L L X V tail tailX tailV inp out
    let SF := { S with R := (Function.update S.R (Fixed.ringReg .out)
      (cstream A w (Fixed.result q l M X V) ++ tail)) }
    ∃ v' n, v'.user = v.user ∧ n ≤ Fixed.cost q l w M ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        Fixed.workspace C q l w M) depth (Fixed.program hQ) (mk v S) n (mk v' SF) ∧
      ∀ j < M, ∀ i < L,
        ‖((2 ^ l : ℕ) : ℂ) * value q (decodeWord
          (((SF.R (Fixed.ringReg .out)).drop ((j * 2 ^ l + i) * w)).take w)) -
          lower (fun k => value q (block (X j) k)) (fun k => value q (block (V j) k)) i‖ ≤
            2 * (2 ^ l : ℕ) / (2 : ℝ) ^ q := by
  dsimp only
  have hr : 1 ≤ 2 ^ l := Nat.one_le_two_pow
  have hL : L ≤ 2 ^ l := by omega
  obtain ⟨v', n, hu, hn, he⟩ := Fixed.exec_with_tails_within (body := body) hQ hA hq hw hL hL hpad
    X V hlenX hlenV hX hV v tail tailX tailV inp out C hpush depth
  refine ⟨v', n, hu, hn, he, ?_⟩
  intro j hj i hi
  simpa only [Function.update_self] using
    lower_output_error hA hw hpad X V hlenX hlenV hX hV tail j hj i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
