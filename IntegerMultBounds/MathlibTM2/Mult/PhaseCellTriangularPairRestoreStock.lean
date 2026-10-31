module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTriangularPairRestore
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTriangularPairStock

/-! Retiring the intermediate operand adds only linear generated-count traffic. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.Spec.SignedRingProduct IntegerMultBounds.NLogN.ToeplitzInverse
variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

private theorem releaseUpperInput_native :
    mnNativePushBound 3 (releaseUpperInput (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [releaseUpperInput,releaseRows,releaseFromDimensions,releasePrefix,unaryProduct,
    transfer,transferAct,ucopy,umulSym,scanP,scanR,drainR,popDo,keepIn,pushN,popPush,
    moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]

theorem triangularPairRestored_with_x_tail_exec_within (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    {q l w M L : ℕ} (hq : 1 ≤ q) (hw : q + 2 ≤ w) (hpad : L + L ≤ 2 ^ l + 1)
    (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (v : HS 117 Q A U) (tail tailX : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (C : ℕ) (hpush : mnProgPush (rpProg (P := P) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hQ) ≤ C) (depth : ℕ) :
    let ys := cstream A w (Fixed.result q l M X (fun n => (V n).reverse)) ++ tail
    let SF := Fixed.startWithTails q l w M L L X V
      (cstream A w (Fixed.result q l M X (upperOperand q l L X V)) ++ ys) tailX [] inp out
    ∃ v' n, v'.user = v.user ∧
      n ≤ 2 * Fixed.cost q l w M +
        2 * (M * (32 * L * w + 19 * L + 17) + 6 * L * w + 9 * L + 20) +
        (M * (20 * L * w + 19 * L + 6 * 2 ^ l * w + 23) +
          4 * w + 6 * 2 ^ l * w + 9 * l + 22) +
        (12 * (M * L * w) + 9 * M + 6 * (L * w) + 9 * L + 18) ∧
      ExecWithin body (fun d z => mnSize z+d ≤
        mnSize (mk v (Fixed.startWithTails q l w M L L X V tail tailX [] inp out))+depth+
          (triangularPairWorkspace C q l w M L+
            3*(12*(M*L*w)+9*M+6*(L*w)+9*L+18)))
        depth (triangularPairRestored hQ) (mk v (Fixed.startWithTails q l w M L L X V tail tailX [] inp out)) n
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
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁, herr⟩ := triangularPair_with_x_tail_exec_within (body := body)
    hQ hA hq hw hpad X V hlenX hlenV hX hV v tail tailX inp out C hpush depth
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := releaseUpperInput_with_x_tail_exec (body := body) hL X V v₁
    (cstream A w (Fixed.result q l M X (fun n => (V n).reverse)) ++ tail)
    (cstream A w (Fixed.result q l M X (upperOperand q l L X V)) ++
      (cstream A w (Fixed.result q l M X (fun n => (V n).reverse)) ++ tail)) tailX inp out
  have ht₂ := mn_native_exec_within he₂ 3 releaseUpperInput_native depth _ (Nat.le_refl _)
  have ht := mn_seq_within_add he₁ ht₂
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,by omega,ht.mono ?_,?_⟩
  · intro d z hz
    omega
  · intro j hj i hi
    simpa [Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank, Fixed.ringReg] using herr j hj i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
