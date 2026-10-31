module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBranchInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTwoBranchesStock

/-! Actual branch batching retains the compact convolution workspace ledger. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.Spec.SignedRingProduct IntegerMultBounds.NLogN.ToeplitzInverse
variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

theorem duplicateStream_native {T : ℕ} (src buf tmp : Fin T) :
    mnNativePushBound 3 (duplicateStream (P := P) (Q := Q) (A := A) (U := U) src buf tmp) := by
  simp [duplicateStream,copyR,copyStep,moveR,moveStep,whileR,peekR,
    mnNativePushBound,mnActPush]

theorem twoBranchesFromSingleInput_with_x_tail_exec_within (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
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
    ∃ v' n, v'.user = v.user ∧ n ≤ 6 * (M * L * w) + 6 + compactPairCost q l w (M + M) L ∧
      ExecWithin body (fun d z => mnSize z+d ≤
        mnSize (mk v (singleBranchInputWithXTail q l w M L X Z V tail tailX inp out))+depth+
          (18*(M*L*w)+18+compactPairWorkspace C q l w (M+M) L))
        depth (twoBranchesFromSingleInput hQ) (mk v (singleBranchInputWithXTail q l w M L X Z V tail tailX inp out)) n
        (mk v' (Fixed.startWithTails q l w (M + M) L L (rowBank M X Z) (rowBank M V V)
          (cstream A w (pairRows q l M L X V ++ pairRows q l M L Z V) ++ tail) tailX [] inp out)) := by
  let S := singleBranchInputWithXTail q l w M L X Z V tail tailX inp out
  let rawV := cstream A w ((List.range M).flatMap V)
  have hlen : ((List.range M).flatMap V).length = M * L := by
    calc
      _ = ((List.range M).map (fun _ => L)).sum := by
        rw [List.length_flatMap]
        congr 1
        apply List.map_congr_left
        intro n hn
        exact hlenV n (List.mem_range.mp hn)
      _ = _ := by simp
  have hraw : rawV.length = M * L * w := by simp [rawV, hlen]
  obtain ⟨v₁, hu₁, he₁⟩ := duplicateStream_exec (body := body)
    (src := 111) (buf := 1) (tmp := 2) (by decide) v S rawV
    (by simp [S, singleBranchInputWithXTail, rawV])
    (by simp [S, singleBranchInputWithXTail, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [S, singleBranchInputWithXTail, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
  have ht₁ := mn_native_exec_within he₁ 3 (duplicateStream_native 111 1 2) depth _ (Nat.le_refl _)
  have he₁' := ht₁.cast (by rw [hraw])
    (congrArg (mk v₁) (branch_input_with_x_tail_frame q l w M L X Z V tail tailX inp out))
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := twoBranches_with_x_tail_exec_within (body := body)
    hQ hA hq hw hpad X Z V hlenX hlenZ hlenV hX hZ hV v₁ tail tailX inp out C hpush depth
  have ht := mn_seq_within_add he₁' he₂
  refine ⟨v₂,(6*(M*L*w)+6)+n₂,hu₂.trans hu₁,by omega,ht.mono ?_⟩
  intro d z hz
  rw [hraw] at hz
  dsimp only [S] at hz
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
