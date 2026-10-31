module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairFinish
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTriangularPairRestoreStock

/-! The compact triangular pair includes both numerical products, all intermediate
retirement, and final result publication in one linear stock ledger. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.Spec.SignedRingProduct IntegerMultBounds.NLogN.ToeplitzInverse
variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

private theorem finishTriangularPair_native :
    mnNativePushBound 3 (finishTriangularPair (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [finishTriangularPair,upperCropFromDimensions,correlationBatch,correlationLoopBody,
    correlationNext,reverseSlice,reverseWords,reverseLoopBody,reverseNext,publishPairResult,
    releaseRingBatch,releaseFromDimensions,releasePrefix,unaryProduct,padding,upow2,udbl,usub,
    copyPrefix,copyR,copyStep,transfer,transferAct,ucopy,umulSym,scanP,scanR,drainR,popDo,
    keepIn,pushN,popPush,dropTop,moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]

def compactPairWorkspace (C q l w M L : ℕ) : ℕ :=
  triangularPairWorkspace C q l w M L+
    3*(12*(M*L*w)+9*M+6*(L*w)+9*L+18)+3*pairFinishCost l w M L

theorem compactTriangularPair_with_x_tail_exec_within (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    {q l w M L : ℕ} (hq : 1 ≤ q) (hw : q + 2 ≤ w) (hpad : L + L ≤ 2 ^ l + 1)
    (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (v : HS 117 Q A U) (tail tailX : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (C : ℕ) (hpush : mnProgPush (rpProg (P := P) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hQ) ≤ C) (depth : ℕ) :
    let SF := Fixed.startWithTails q l w M L L X V (cstream A w (pairRows q l M L X V) ++ tail) tailX [] inp out
    ∃ v' n, v'.user = v.user ∧ n ≤ compactPairCost q l w M L ∧
      ExecWithin body (fun d z => mnSize z+d ≤
        mnSize (mk v (Fixed.startWithTails q l w M L L X V tail tailX [] inp out))+depth+
          compactPairWorkspace C q l w M L) depth (compactTriangularPair hQ) (mk v (Fixed.startWithTails q l w M L L X V tail tailX [] inp out)) n (mk v' SF) ∧
      ∀ j < M, ∀ i : Fin L,
        ‖((2 ^ l : ℕ) : ℂ) * value q (decodeWord
          (((SF.R (Fixed.ringReg .out)).drop ((j * L + (L - 1 - i.val)) * w)).take w)) -
          lower (fun k => value q (block (X j) k))
            (fun k => value q (block (upperOperand q l L X V j) k)) i.val‖ ≤
          2 * (2 ^ l : ℕ) / (2 : ℝ) ^ q := by
  dsimp only
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁, _⟩ := triangularPairRestored_with_x_tail_exec_within (body := body)
    hQ hA hq hw hpad X V hlenX hlenV hX hV v tail tailX inp out C hpush depth
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := finishTriangularPair_with_x_tail_exec (body := body)
    hA hw hpad X V hlenX hlenV hX hV v₁ tail tailX inp out
  have ht₂ := mn_native_exec_within he₂ 3 finishTriangularPair_native depth _ (Nat.le_refl _)
  have ht := mn_seq_within_add he₁ ht₂
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,by unfold compactPairCost; omega,ht.mono ?_,?_⟩
  · intro d z hz
    dsimp only [compactPairWorkspace]
    omega
  ·
    have hr : 1 ≤ 2 ^ l := Nat.one_le_two_pow
    have hL : L ≤ 2 ^ l := by omega
    intro j hj i
    simpa [Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank, Fixed.ringReg, pairRows] using
      lowerRows_error hA hw hpad X (upperOperand q l L X V) hlenX
        (fun n _ => upperOperand_length hL X V n) hX
        (upperOperand_disk hpad X V hlenX hlenV hX hV) tail j hj i


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
