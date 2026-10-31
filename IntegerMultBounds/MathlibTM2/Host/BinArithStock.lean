module

public import IntegerMultBounds.MathlibTM2.Host.BinArith
public import IntegerMultBounds.MathlibTM2.StackNativeStock
public import IntegerMultBounds.MathlibTM2.StackExecutionUnique
public import IntegerMultBounds.MathlibTM2.StackLoopBoundary

/-! Counting reuses its scratch: neither increment nor the symbol loop
increases stock. Unary-to-binary allocation is paid only once. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {s t : Store (HΓ (T := T) A) (HS T Q A U)} {n : ℕ}

private theorem flag_nonempty (z : Store (HΓ (T := T) A) (HS T Q A U)) (i : Fin T)
    (hz : z.var.flag = (z.stk (.rt i)).head?.isSome) (hf : z.var.flag = true) :
    z.stk (.rt i) ≠ [] := by
  intro he
  simp [he] at hz
  simp [hz] at hf

private theorem peek_within (i : Fin T) (z : Store (HΓ (T := T) A) (HS T Q A U))
    (depth B : ℕ) (hb : mnSize z+depth ≤ B) :
    ExecWithin body (fun d z => mnSize z+d ≤ B) depth (.act (peekR i)) z 1 ((peekR i).run z) := by
  have hg := mn_act_size (peekR (Q := Q) (A := A) (U := U) i) z
  change mnSize ((peekR i).run z) ≤ mnSize z+0 at hg
  exact .act _ _ hb (by omega)

theorem moveR_within (i j : Fin T) (f : Fin (A+4) → Fin (A+4))
    (he : Exec body (moveR i j f) s n t) (depth B : ℕ) (hb : mnSize s+depth ≤ B) :
    ExecWithin body (fun d z => mnSize z+d ≤ B) depth (moveR i j f) s n t := by
  cases he with
  | seq hp hq =>
    cases hp
    have hw := peek_within (body := body) i s depth B hb
    refine .seq hw (loop_action_within body (moveStep i j f) (·.flag)
      (fun z => z.var.flag = (z.stk (.rt i)).head?.isSome) ?_ hq rfl depth B hw.final)
    intro z hz hf
    refine ⟨?_,mn_pop_one_push z (.rt i) _ _ (by simp [mnActPush,peekR]) (flag_nonempty z i hz hf)⟩
    simp [moveStep,peekR,Action.run]

theorem incrField_within (a tmp cy : Fin T) (he : Exec body (incrField a tmp cy) s n t)
    (depth B : ℕ) (hb : mnSize s+depth ≤ B) :
    ExecWithin body (fun d z => mnSize z+d ≤ B) depth (incrField a tmp cy) s n t := by
  cases he with
  | seq hp hr =>
    cases hp
    cases hr with
    | seq hq hr =>
      have hw := peek_within (body := body) a s depth B hb
      have hl := loop_action_within body (incStep a tmp cy) (·.flag)
        (fun z => z.var.flag = (z.stk (.rt a)).head?.isSome) (by
          intro z hz hf
          refine ⟨?_,mn_pop_one_push z (.rt a) _ _ (by simp [mnActPush,peekR]) (flag_nonempty z a hz hf)⟩
          simp [incStep,peekR,Action.run]) hq rfl depth B hw.final
      exact .seq hw (.seq hl (moveR_within tmp a id hr depth B hl.final))

theorem countIter_within (c tmp cy : Fin T) (he : Exec body (countIter c tmp cy) s n t)
    (depth B : ℕ) (hb : mnSize s+depth ≤ B) :
    ExecWithin body (fun d z => mnSize z+d ≤ B) depth (countIter c tmp cy) s n t := by
  cases he with
  | seq hp hq =>
    have hw := mn_native_exec_within hp 0 (by simp [mnNativePushBound,setCarry,mnActPush]) depth B (by omega)
    exact .seq hw (incrField_within c tmp cy hq depth B hw.final)

theorem eachSym_within (a saved : Fin T) (p : Pr P T Q A U)
    (hp : ∀ s t n depth B, Exec body p s n t → mnSize s+depth ≤ B →
      ExecWithin body (fun d z => mnSize z+d ≤ B) depth p s n t)
    (he : Exec body (eachSym a saved p) s n t) (depth B : ℕ) (hb : mnSize s+depth ≤ B) :
    ExecWithin body (fun d z => mnSize z+d ≤ B) depth (eachSym a saved p) s n t := by
  cases he with
  | seq hpeek hloop =>
    cases hpeek
    have hw := peek_within (body := body) a s depth B hb
    refine .seq hw (loop_within_of_boundary body _ (·.flag)
      (fun z => z.var.flag = (z.stk (.rt a)).head?.isSome ∧ mnSize z+depth ≤ B)
      (fun d z => mnSize z+d ≤ B) depth (fun z hz => hz.2) ?_ hloop ⟨rfl,hw.final⟩)
    intro z z' k hz hf hex
    cases hex with
    | seq hpop hrest =>
      cases hpop
      have hg := mn_pop_one_push z (.rt a) (fun v o => {v with sym := o})
        (.push (.rt saved) (fun v => v.sym.getD blank) .done) (by simp [mnActPush])
        (flag_nonempty z a hz.1 hf)
      change mnSize ((popPush a saved).run z) ≤ mnSize z at hg
      have hpop := ExecWithin.act (body := body) (Inv := fun d z => mnSize z+d ≤ B)
        (d := depth) (popPush a saved) z hz.2 ((Nat.add_le_add_right hg depth).trans hz.2)
      cases hrest with
      | seq hbody hpeek =>
        have hbody := hp _ _ _ depth B hbody hpop.final
        cases hpeek
        have hpeek := peek_within (body := body) a _ depth B hbody.final
        exact ⟨.seq hpop (.seq hbody hpeek),rfl,hpeek.final⟩


theorem toBinary_within (u wR c saved tmp cy : Fin T)
    (hreg : [u,wR,c,saved,tmp].Nodup) (v : HS T Q A U) (S : Stacks T A)
    (hsaved : S.R saved = []) {n : ℕ} {f : Store (HΓ (T := T) A) (HS T Q A U)}
    (he : Exec body (toBinary u wR c saved tmp cy) (mk v S) n f) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤
      mnSize (mk v S)+depth+2*(4*(S.R wR).length+4)) depth
      (toBinary u wR c saved tmp cy) (mk v S) n f := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₀,_,hz⟩ := bzero_exec body (wR := wR) (c := c) (t := saved) (by regs_nodup) v S hsaved
  cases he with
  | seq hzero hrest =>
    obtain ⟨hsteps,_⟩ := hzero.unique hz
    have hw := mn_native_exec_within hzero 2 (by
      simp [bzero,zeroBits,umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,whileR,moveStep,peekR,
        mnNativePushBound,mnActPush]) depth
      (mnSize (mk v S)+depth+2*(4*(S.R wR).length+4)) (by rw [hsteps])
    cases hrest with
    | seq hloop hmove =>
      have hl := eachSym_within u saved (countIter c tmp cy)
        (fun s t n d B he hb => countIter_within c tmp cy he d B hb) hloop depth _ hw.final
      exact .seq hw (.seq hl (moveR_within saved u id hmove depth _ hl.final))


/-- The original conversion specification, with a width-only scratch reserve. -/
theorem toBinary_exec_within {u wR c saved tmp : Fin T}
    (hreg : [u,wR,c,saved,tmp].Nodup) (cy : Fin T) (v : HS T Q A U) (S : Stacks T A)
    (hc : S.R c = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (S.R u).length*(4*(S.R wR).length+10)+4*(S.R wR).length+8 ∧
      ExecWithin body (fun d z => mnSize z+d ≤
        mnSize (mk v S)+depth+2*(4*(S.R wR).length+4)) depth
        (toBinary u wR c saved tmp cy) (mk v S) n
        (mk v' {S with R := Function.update S.R c (binSyms (S.R wR).length (S.R u).length)}) := by
  obtain ⟨v',n,hu,hn,he⟩ := toBinary_exec (body := body) hreg cy v S hc hsaved htmp
  exact ⟨v',n,hu,hn,toBinary_within u wR c saved tmp cy hreg v S hsaved he depth⟩

end IntegerMultBounds.MathlibTM2.Host
