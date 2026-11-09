module

public import IntegerMultBounds.MathlibTM2.Mult.ClearRegisterBank
public import IntegerMultBounds.MathlibTM2.Host.BinArithStock

/-! Structural two-sided bank cleanup never increases tape stock. Moving the
left side to the right reuses storage; the following clear only discards it. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {s t : Store (HΓ (T := T) A) (HS T Q A U)} {n : ℕ}

private theorem moveLR_within (r : Fin T) (p : Fin (A+4) → Bool)
    (he : Exec body (WordCmd.moveLR r p) s n t) (depth B : ℕ) (hb : mnSize s+depth ≤ B) :
    ExecWithin body (fun d z => mnSize z+d ≤ B) depth (WordCmd.moveLR r p) s n t := by
  cases he with
  | seq hp hq =>
    cases hp
    have hg := mn_act_size (WordCmd.peekL (Q := Q) (A := A) (U := U) r p) s
    change mnSize ((WordCmd.peekL r p).run s) ≤ mnSize s+0 at hg
    have hw : ExecWithin body (fun d z => mnSize z+d ≤ B) depth
        (.act (WordCmd.peekL r p)) s 1 ((WordCmd.peekL r p).run s) :=
      .act _ _ hb (by omega)
    refine .seq hw (loop_action_within body (WordCmd.lrStep r p) (·.flag)
      (fun z => z.var.flag = ((z.stk (.lt r)).head?.map p).getD false) ?_ hq rfl depth B hw.final)
    intro z hz hf
    have hne : z.stk (.lt r) ≠ [] := by
      intro he
      simp [he] at hz
      simp [hz] at hf
    refine ⟨?_,mn_pop_one_push z (.lt r) _ _ (by simp [mnActPush,WordCmd.peekL]) hne⟩
    simp [WordCmd.lrStep,WordCmd.peekL,Action.run]

theorem clearRegister_within (r : Fin T) (he : Exec body (clearRegister r) s n t)
    (depth B : ℕ) (hb : mnSize s+depth ≤ B) :
    ExecWithin body (fun d z => mnSize z+d ≤ B) depth (clearRegister r) s n t := by
  cases he with
  | seq hmove hclear =>
    have hw := moveLR_within r (fun _ => true) hmove depth B hb
    refine .seq hw (mn_native_exec_within hclear 0 ?_ depth B ?_)
    · simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]
    · simpa using hw.final

theorem clearRegisters_within (rs : List (Fin T)) (he : Exec body (clearRegisters rs) s n t)
    (depth B : ℕ) (hb : mnSize s+depth ≤ B) :
    ExecWithin body (fun d z => mnSize z+d ≤ B) depth (clearRegisters rs) s n t := by
  induction rs generalizing s t n with
  | nil =>
    apply mn_native_exec_within he 0 (by simp [clearRegisters,mnNativePushBound,mnActPush]) depth B
    simpa using hb
  | cons r rs ih =>
    cases he with
    | seq hclear hrest =>
      have hw := clearRegister_within r hclear depth B hb
      exact .seq hw (ih hrest hw.final)

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
