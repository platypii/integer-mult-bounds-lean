module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConditionalHaloGroupPreparation
public import IntegerMultBounds.MathlibTM2.Host.ClearBankExcept
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Header copies cost linear stock; the empty exit allocates no symbols.
The origin controller's reserve is supplied separately from native traffic. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

theorem installHaloGroupHeaders_native :
    mnNativePushBound 2 (installHaloGroupHeaders (P₀ := P) (Q := Q) (A := A) (U := U)) :=
  ⟨copyUnaryHeaders_native _ _,copyUnaryHeaders_native _ _⟩

theorem releaseEmptyHaloGroup_native :
    mnNativePushBound 0 (releaseEmptyHaloGroup (P := P) (Q := Q) (A := A) (U := U)) := by
  refine ⟨⟨clearWords_native_zero _,clearWords_native_zero _⟩,?_⟩
  simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]

/-- Neither branch of the empty-class cleanup, nor the final flag probe,
needs a space allowance. This applies to either value of the runtime flag. -/
theorem conditionalHaloPreparationExit_native :
    mnNativePushBound 0
      (.seq (.cond (fun v : HS 144 Q A U => v.flag) (.act .done)
        (releaseEmptyHaloGroup (P := P))) (.act (peekR 116))) := by
  exact ⟨⟨Nat.zero_le _,releaseEmptyHaloGroup_native⟩,Nat.zero_le _⟩

/-- Compose over arbitrary stores, leaving concrete header banks and controller
endpoints to the correctness proof. Cleanup shares the controller's reserve. -/
theorem conditionalHaloGroupPreparation_trace_within
    {v₀ v₁ v₂ v₃ : HS 144 Q A U} {S₀ S₁ S₂ S₃ : Stacks 144 A}
    {m₁ m₂ m₃ work cap : ℕ}
    (h₁ : Exec (embTab groupReg body) installHaloGroupHeaders
      (mk v₀ S₀) m₁ (mk v₁ S₁))
    (h₂ : ExecWithin (embTab groupReg body)
      (fun d z => mnSize z+d ≤ mnSize (mk v₁ S₁)+0+work) 0
      (embProg groupReg id probeAndGatherHaloControls) (mk v₁ S₁) m₂ (mk v₂ S₂))
    (h₃ : Exec (embTab groupReg body)
      (.seq (.cond (·.flag) (.act .done) releaseEmptyHaloGroup) (.act (peekR 116)))
      (mk v₂ S₂) m₃ (mk v₃ S₃))
    (hcap : 2*m₁+work ≤ cap) :
    ExecWithin (embTab groupReg body)
      (fun d z => mnSize z+d ≤ mnSize (mk v₀ S₀)+0+cap) 0
      conditionalHaloGroupPreparation (mk v₀ S₀) (m₁+(m₂+m₃)) (mk v₃ S₃) := by
  have ht₁ := mn_native_exec_within h₁ 2 installHaloGroupHeaders_native 0 _ (Nat.le_refl _)
  have ht₃ := mn_native_exec_within h₃ 0 conditionalHaloPreparationExit_native 0 _ (Nat.le_refl _)
  exact (mn_seq_within_add ht₁ (mn_seq_within_add h₂ ht₃)).mono (by intro d z hz; omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
