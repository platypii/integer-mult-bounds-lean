module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTrimAdvance

/-! A counted scan converts inter-origin advances to publication gaps while
saving the original controls and count for final restoration. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

def trimAdvanceUpdate (R : Regs T A) (count savedCount control savedControl acc : Fin T)
    (cs zs ct ss ys : List (Fin (A+4))) : Regs T A :=
  Function.update (Function.update (Function.update (Function.update (Function.update R count cs)
    savedCount (zs++R savedCount)) control ct) savedControl (ss++R savedControl)) acc (ys++R acc)

theorem trimAdvanceUpdate_comp {count savedCount control savedControl acc : Fin T}
    (hreg : [count,savedCount,control,savedControl,acc].Nodup) (R : Regs T A)
    (cs zs ct ss ys cs' zs' ct' ss' ys' : List (Fin (A+4))) :
    trimAdvanceUpdate (trimAdvanceUpdate R count savedCount control savedControl acc cs zs ct ss ys)
      count savedCount control savedControl acc cs' zs' ct' ss' ys' =
    trimAdvanceUpdate R count savedCount control savedControl acc cs' (zs'++zs) ct' (ss'++ss) (ys'++ys) := by
  have hr := hreg
  regs_ne hr
  funext k
  simp only [trimAdvanceUpdate,Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all only [ne_eq,eq_self,not_false_eq_true,List.append_assoc]

def trimAdvanceLoopBody (count savedCount control savedControl counter window acc trash tmp : Fin T) : Pr P T Q A U :=
  .seq (.act (popPush count savedCount)) <|
  .seq (trimAdvance control savedControl counter window acc trash tmp) (.act (peekR count))

theorem trimAdvanceLoop_exec {count savedCount control savedControl counter window acc trash tmp : Fin T}
    (hreg : [count,savedCount,control,savedControl,counter,window,acc,trash,tmp].Nodup)
    (L : ℕ) (ds : List ℕ) (hLd : ∀ d ∈ ds, L ≤ d) (cs tail : List (Fin (A+4)))
    (hlen : cs.length = ds.length) (v : HS T Q A U) (S : Stacks T A)
    (hc : S.R count = cs) (hs : S.R control = gatherControls A ds++tail)
    (hw : (S.R window).length = L) (hz : ∀ k ∈ [counter,trash,tmp], S.R k = [])
    (hflag : v.flag = cs.head?.isSome) :
    ∃ v', v'.user = v.user ∧
      Exec body (.loop (·.flag) (trimAdvanceLoopBody count savedCount control savedControl counter window acc trash tmp))
        (mk v S) (ds.length*(4*L+15)+4*ds.sum+1)
        (mk v' { S with R := (trimAdvanceUpdate S.R count savedCount control savedControl acc []
          cs.reverse tail (gatherControls A ds).reverse (gatherControls A (ds.map (·-L))).reverse) }) := by
  have hr := hreg
  regs_ne hr
  have heffect : [count,savedCount,control,savedControl,acc].Nodup := by regs_nodup
  induction ds generalizing cs v S with
  | nil =>
    have hnil : cs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    have he := Exec.loop_false (body := body)
      (p := trimAdvanceLoopBody count savedCount control savedControl counter window acc trash tmp)
      (s := mk v S) (by simpa [hnil] using hflag)
    refine ⟨v,rfl,he.cast (by simp) ?_⟩
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    simp only [trimAdvanceUpdate,hnil,gatherControls,List.map_nil,List.reverse_nil,List.nil_append,Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all only [ne_eq,eq_self,not_false_eq_true]
  | cons d ds ih =>
    cases cs with
    | nil => simp at hlen
    | cons c cs =>
      let S₀ : Stacks T A := { S with R := (Function.update (Function.update S.R count cs) savedCount (c::S.R savedCount)) }
      let v₀ : HS T Q A U := { v with sym := some c }
      have hpop : (popPush count savedCount : Act T Q A U).run (mk v S) = mk v₀ S₀ := by
        simp [popPush,Action.run,update_rt,hc,S₀,v₀,‹count ≠ savedCount›.symm]
      obtain ⟨v₁,hu₁,he₁⟩ := trimAdvance_exec (body := body)
        (show [control,savedControl,counter,window,acc,trash,tmp].Nodup by regs_nodup)
        L d (hLd d (by simp)) (gatherControls A ds++tail) v₀ S₀
        (by simpa (disch := first | assumption | (apply Ne.symm; assumption)) [S₀,gatherControls,List.append_assoc] using hs)
        (by simpa (disch := first | assumption | (apply Ne.symm; assumption)) [S₀] using hw) (by
          intro k hk
          have hh := hz k hk
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl
          all_goals simpa (disch := first | assumption | (apply Ne.symm; assumption)) [S₀] using hh)
      let S₁ : Stacks T A := { S with R := (trimAdvanceUpdate S.R count savedCount control savedControl acc
        cs [c] (gatherControls A ds++tail) (blank::List.replicate d tick)
        (blank::List.replicate (d-L) tick)) }
      have he₁' : Exec body (trimAdvance control savedControl counter window acc trash tmp)
          (mk v₀ S₀) (4*L+4*d+12) (mk v₁ S₁) := by
        refine he₁.cast rfl ?_
        congr 1
        ext1
        · rfl
        · rfl
        · rfl
        funext k
        simp only [S₁,S₀,trimAdvanceUpdate,Function.update_apply,List.cons_append,List.nil_append]
        split_ifs <;> subst_vars <;> simp_all only [ne_eq,eq_self,not_false_eq_true]
      have stable (k : Fin T) (hkc : k ≠ count) (hkz : k ≠ savedCount) (hks : k ≠ control)
          (hkss : k ≠ savedControl) (hka : k ≠ acc) : S₁.R k = S.R k := by
        simp [S₁,trimAdvanceUpdate,hkc,hkz,hks,hkss,hka]
      have hc₁ : S₁.R count = cs := by
        simp (disch := first | assumption | (apply Ne.symm; assumption)) [S₁,trimAdvanceUpdate]
      have hs₁ : S₁.R control = gatherControls A ds++tail := by
        simp (disch := first | assumption | (apply Ne.symm; assumption)) [S₁,trimAdvanceUpdate]
      have hz₁ : ∀ k ∈ [counter,trash,tmp], S₁.R k = [] := by
        intro k hk
        have hh := hz k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl
        all_goals rw [stable _ (by first | assumption | (apply Ne.symm; assumption))
          (by first | assumption | (apply Ne.symm; assumption))
          (by first | assumption | (apply Ne.symm; assumption))
          (by first | assumption | (apply Ne.symm; assumption))
          (by first | assumption | (apply Ne.symm; assumption))]; exact hh
      have hp := Exec.act (body := body) (peekR count) (mk v₁ S₁)
      rw [peekR_run,hc₁] at hp
      obtain ⟨v₂,hu₂,he₂⟩ := ih (fun d hd => hLd d (by simp [hd])) cs (by simpa using hlen)
        { v₁ with flag := cs.head?.isSome } S₁ hc₁ hs₁
        (by rw [stable _ ‹count ≠ window›.symm ‹savedCount ≠ window›.symm
          ‹control ≠ window›.symm ‹savedControl ≠ window›.symm ‹window ≠ acc›]; exact hw) hz₁ rfl
      have hstep : Exec body (trimAdvanceLoopBody count savedCount control savedControl counter window acc trash tmp)
          (mk v S) (4*L+4*d+14) (mk { v₁ with flag := cs.head?.isSome } S₁) := by
        exact (Exec.seq (hpop ▸ Exec.act (body := body) (popPush count savedCount) _) (Exec.seq he₁' hp)).cast (by omega) rfl
      refine ⟨v₂,hu₂.trans hu₁,(Exec.loop_true (by simpa using hflag) hstep he₂).cast ?_ ?_⟩
      · simp only [List.length_cons,List.sum_cons]; ring
      · congr 1
        ext1
        · rfl
        · rfl
        · rfl
        change trimAdvanceUpdate (trimAdvanceUpdate S.R count savedCount control savedControl acc _ _ _ _ _)
          count savedCount control savedControl acc _ _ _ _ _ = _
        rw [trimAdvanceUpdate_comp heffect]
        simp only [gatherControls,List.map_cons,List.reverse_cons,List.reverse_append,List.reverse_replicate,
          List.append_assoc,List.singleton_append]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
