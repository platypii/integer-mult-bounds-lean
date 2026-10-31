module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMergedBranches
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBranchInputStock

/-! Four triangular products, one RHS duplication and actual branch subtraction
share the certified numerical reserve plus linear native traffic. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

theorem fixedBranchMerge_native :
    mnNativePushBound 3 (fixedBranchMerge (P := P) (Q := Q) (A := A) (U := U)) := by
  have hmerge (a b dst width tmp : Fin 117) :
      mnNativePushBound 3 (mergeStream (P := P) (Q := Q) (A := A) (U := U) a b dst width tmp) :=
    autoWords_native _ _ _ _ _ _ (by decide) (by decide)
  simp [fixedBranchMerge,branchWords,halfCount,halfPairAct,mergeFromWords,mergePair,hmerge,
    takePrefix,unaryProduct,transfer,transferAct,ucopy,umulSym,scanP,scanR,drainR,popDo,
    keepIn,pushN,popPush,moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]

theorem mergedBranches_with_x_tail_exec_within (hQ : rpStates ≤ Q) (hA : 96 ≤ A)
    {q l w M L : ℕ} (hq : 1 ≤ q) (hw : q + 2 ≤ w) (hpad : L + L ≤ 2 ^ l + 1)
    (X Z V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenZ : ∀ n < M, (Z n).length = L)
    (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hZ : ∀ n < M, ∀ z ∈ Z n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (v : HS 117 Q A U) (tail tailX : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (C : ℕ) (hpush : mnProgPush (rpProg (P := P) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hQ) ≤ C) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 6 * (M * L * w) + 6 + compactPairCost q l w (M + M) L + fixedMergeCost w M L ∧
      ExecWithin body (fun d z => mnSize z+d ≤
        mnSize (mk v (singleBranchInputWithXTail q l w M L X Z V tail tailX inp out))+depth+
          (18*(M*L*w)+18+compactPairWorkspace C q l w (M+M) L+3*fixedMergeCost w M L))
        depth (mergedBranches hQ) (mk v (singleBranchInputWithXTail q l w M L X Z V tail tailX inp out)) n
        (mk v' (Fixed.startWithTails q l w (M + M) L L (rowBank M X Z) (rowBank M V V)
          (cstream A w (branchDifference q l M L X Z V) ++ tail) tailX [] inp out)) := by
  have hr : 1 ≤ 2 ^ l := Nat.one_le_two_pow
  have hL : L ≤ 2 ^ l := by omega
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := twoBranchesFromSingleInput_with_x_tail_exec_within (body := body)
    hQ (by omega) hq hw hpad X Z V hlenX hlenZ hlenV hX hZ hV v tail tailX inp out C hpush depth
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := fixedBranchMerge_with_x_tail_exec (body := body)
    (q := q) (l := l) (w := w) (M := M) (L := L) hA (by omega)
    (rowBank M X Z) (rowBank M V V) (pairNumerator q l M L X V)
    (pairNumerator q l M L Z V) v₁ tail tailX inp out
  simp only [pairNumerator_stream q l M L hL] at he₂
  rw [cstream_append, List.append_assoc] at he₁
  have ht₂ := mn_native_exec_within he₂ 3 fixedBranchMerge_native depth _ (Nat.le_refl _)
  have ht := mn_seq_within_add he₁ ht₂
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,by omega,ht.mono ?_⟩
  intro d z hz
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
