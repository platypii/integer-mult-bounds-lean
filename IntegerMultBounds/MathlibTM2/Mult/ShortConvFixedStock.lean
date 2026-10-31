module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvFixed
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvBatchUnaryStock

/-! The fixed 117-tape convolution program carries the complete resource trace,
including its generated header/counters and final retirement. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.Fixed
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.Spec.SignedRingProduct
variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

/-- Uniform in the raw operand lengths: shared setup plus linear batch data. -/
def workspace (C p l w M : ℕ) : ℕ :=
  3*batchSetupCost p l w (2^l) (2^l)+(C+1)*rpWorkspace p l w 0+
    (1842*(C+1)+120)*(M*2^l*w)+150*M+48

private theorem workspace_bound (C p l w M a b : ℕ) (ha : a ≤ 2^l) (hb : b ≤ 2^l) :
    3*batchSetupCost p l w a b+3*batchPackCost M (2^l) w a+
      3*batchPackCost M (2^l) w b+(C+1)*rpWorkspace p l w M ≤ workspace C p l w M := by
  have hsetup : batchSetupCost p l w a b ≤ batchSetupCost p l w (2^l) (2^l) := by
    have ha₁ := Nat.mul_le_mul_right (4*w+9) ha
    have hb₁ := Nat.mul_le_mul_right (4*w+9) hb
    have ha₂ := Nat.mul_le_mul_right w ha
    have hb₂ := Nat.mul_le_mul_right w hb
    unfold batchSetupCost operandSetupCost
    omega
  have hbatch := batchProgram_stock_le C p l w M a b ha hb
  unfold workspace
  omega

theorem exec_with_tails_within (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    {p l w M a b : ℕ} (hp : 1 ≤ p) (hw : p + 2 ≤ w)
    (ha : a ≤ 2 ^ l) (hb : b ≤ 2 ^ l) (hab : a + b ≤ 2 ^ l + 1)
    (X Y : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = a) (hlenY : ∀ n < M, (Y n).length = b)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (hY : ∀ n < M, ∀ z ∈ Y n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (v : HS 117 Q A U) (tail tailX tailY : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (C : ℕ) (hpush : mnProgPush (rpProg (P := P) (Q := Q) (A := A) (U := U)
      ringReg hostReg layout.ι_inj (by decide) hQ) ≤ C) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ cost p l w M ∧
      ExecWithin body (fun d z => mnSize z+d ≤
        mnSize (mk v (startWithTails p l w M a b X Y tail tailX tailY inp out))+depth+
          workspace C p l w M) depth (program hQ) (mk v (startWithTails p l w M a b X Y tail tailX tailY inp out)) n
        (mk v' { startWithTails p l w M a b X Y tail tailX tailY inp out with R :=
          (Function.update (inputBankWithTails p l w M a b X Y tail tailX tailY) (ringReg .out)
            (cstream A w (result p l M X Y) ++ tail)) }) := by
  let S := startWithTails p l w M a b X Y tail tailX tailY inp out
  have clean : RpClean hostReg S := by
    refine ⟨fun _ => rfl, fun k _ => ?_⟩
    have hk := k.isLt
    simp [S, startWithTails, start, inputBankWithTails, inputBank, hostReg,
      show k.val ≠ 94 by omega, show k.val ≠ 100 by omega,
      show k.val ≠ 101 by omega, show k.val ≠ 102 by omega,
      show k.val ≠ 103 by omega, show k.val ≠ 108 by omega,
      show k.val ≠ 110 by omega, show k.val ≠ 111 by omega, show k.val ≠ 93 by omega]
  have setupEmpty : ∀ s ∈ setupWritten ++ setupScratch, S.R (setupReg s) = [] := by
    intro s hs
    simp only [setupWritten, setupScratch, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hs
    rcases hs with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl) <;>
      simp [S, startWithTails, start, inputBankWithTails, inputBank, setupReg]
  have scratchEmpty : ∀ k ∈ [batchReg .recordSaved, batchReg .saved, batchReg .acc,
      batchReg .buf, batchReg .savedBlock, batchReg .tmp], S.R k = [] := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [S, startWithTails, start, inputBankWithTails, inputBank, batchReg]
  have ringEmpty : ∀ r ∈ [RpReg.xs, .ys, .sv, .ta, .tb, .acc, .tmp, .d1, .d2, .d3],
      S.R (ringReg r) = [] := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [S, startWithTails, start, inputBankWithTails, inputBank, ringReg]
  obtain ⟨v', n, hu, hn, he⟩ := batchFromUnary_prefix_exec_within (body := body) layout (by decide) hQ hA
    setupReg setupReg_injective rfl rfl counts_off counts_private hp hw ha hb hab X Y
    hlenX hlenY hX hY (batchReg .records) (batchReg .recordSaved) (batchReg .srcX) (batchReg .srcY)
    (batchReg .saved) (batchReg .acc) (batchReg .buf) (batchReg .savedBlock) (batchReg .tmp)
    packX_distinct packY_distinct packY_off data_off v S tailX tailY clean
    (by simp [S, startWithTails, start, inputBankWithTails, inputBank, setupReg]) (by simp [S, startWithTails, start, inputBankWithTails, inputBank, setupReg])
    (by simp [S, startWithTails, start, inputBankWithTails, inputBank, setupReg]) (by simp [S, startWithTails, start, inputBankWithTails, inputBank, setupReg])
    (by simp [S, startWithTails, start, inputBankWithTails, inputBank, setupReg]) setupEmpty
    (by simp [S, startWithTails, start, inputBankWithTails, inputBank, batchReg])
    (by simp [S, startWithTails, start, inputBankWithTails, inputBank, batchReg]) (by simp [S, startWithTails, start, inputBankWithTails, inputBank, batchReg])
    scratchEmpty ringEmpty C hpush depth
  refine ⟨v', n, hu, hn.trans (batchUnaryCost_le_linear p l w M a b (by omega) ha hb), ?_⟩
  have hout : inputBankWithTails p l w M a b X Y tail tailX tailY (ringReg .out) = tail := by
    simp [inputBankWithTails, inputBank, ringReg]
  have ht := he.mono (by
    intro d z hz
    exact hz.trans (Nat.add_le_add_left (workspace_bound C p l w M a b ha hb) _))
  simpa only [program, S, startWithTails, start, hout, result] using ht

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.Fixed
