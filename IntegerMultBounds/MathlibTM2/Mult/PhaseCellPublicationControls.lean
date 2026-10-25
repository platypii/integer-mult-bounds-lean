module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationRestore

/-! Generate publication gaps from the already computed gather advances.
The first origin is retained; each subsequent advance loses one window.
Original controls, batch count, scratch and borrowed suffixes are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

theorem sum_trimAdvances (L : ℕ) (ds : List ℕ) (hLd : ∀ d ∈ ds, L ≤ d) :
    (ds.map (·-L)).sum+ds.length*L = ds.sum := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    have hd := hLd d (by simp)
    have ht := ih (fun d hd => hLd d (by simp [hd]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

def publicationControls (count savedCount control savedControl counter window zero acc dst trash tmp : Fin T) : Pr P T Q A U :=
  .seq (trimAdvance control savedControl counter zero acc trash tmp) <|
  .seq (.act (popPush count savedCount)) <|
  .seq (.act (peekR count)) <|
  .seq (.loop (·.flag) (trimAdvanceLoopBody count savedCount control savedControl counter window acc trash tmp)) <|
  .seq (moveR acc dst id) <|
  .seq (moveR savedControl control id) (moveR savedCount count id)

theorem publicationControls_exec {count savedCount control savedControl counter window zero acc dst trash tmp : Fin T}
    (hreg : [count,savedCount,control,savedControl,counter,window,zero,acc,dst,trash,tmp].Nodup)
    (L d : ℕ) (ds : List ℕ) (hLd : ∀ d ∈ ds, L ≤ d)
    (c : Fin (A+4)) (cs tail : List (Fin (A+4))) (hlen : cs.length = ds.length)
    (v : HS T Q A U) (S : Stacks T A)
    (hc : S.R count = c::cs) (hs : S.R control = gatherControls A (d::ds)++tail)
    (hw : (S.R window).length = L)
    (hz : ∀ k ∈ [savedCount,savedControl,counter,zero,acc,trash,tmp], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 12*(d+ds.sum)+21*(ds.length+1)+21 ∧
      Exec body (publicationControls count savedCount control savedControl counter window zero acc dst trash tmp)
        (mk v S) n
        (mk v' { S with R := Function.update S.R dst (gatherControls A (d::ds.map (·-L))++S.R dst) }) := by
  have hr := hreg
  regs_ne hr
  have hzc := hz savedCount (by simp)
  have hzs := hz savedControl (by simp)
  have hza := hz acc (by simp)
  obtain ⟨v₁,hu₁,he₁⟩ := trimAdvance_exec (body := body)
    (show [control,savedControl,counter,zero,acc,trash,tmp].Nodup by regs_nodup)
    0 d (Nat.zero_le _) (gatherControls A ds++tail) v S
    (by simpa [gatherControls,List.append_assoc] using hs)
    (by simp [hz zero (by simp)]) (fun k hk => hz k (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
      rcases hk with rfl | rfl | rfl <;> simp))
  let S₁ : Stacks T A := { S with R := (Function.update (Function.update (Function.update S.R control
    (gatherControls A ds++tail)) savedControl (blank::List.replicate d tick)) acc (blank::List.replicate d tick)) }
  have he₁' : Exec body (trimAdvance control savedControl counter zero acc trash tmp)
      (mk v S) (4*d+12) (mk v₁ S₁) := by simpa [S₁,hzs,hza] using he₁
  let S₂ : Stacks T A := { S₁ with R := (Function.update (Function.update S₁.R count cs) savedCount [c]) }
  let v₂ : HS T Q A U := { v₁ with sym := some c }
  have hpop : (popPush count savedCount : Act T Q A U).run (mk v₁ S₁) = mk v₂ S₂ := by
    simp (disch := first | assumption | (apply Ne.symm; assumption))
      [popPush,Action.run,update_rt,S₂,S₁,v₂,hc,hzc]
  have hc₂ : S₂.R count = cs := by simp [S₂,‹count ≠ savedCount›]
  have hp := Exec.act (body := body) (peekR count) (mk v₂ S₂)
  rw [peekR_run,hc₂] at hp
  obtain ⟨v₃,hu₃,he₃⟩ := trimAdvanceLoop_exec (body := body)
    (show [count,savedCount,control,savedControl,counter,window,acc,trash,tmp].Nodup by regs_nodup)
    L ds hLd cs tail hlen { v₂ with flag := cs.head?.isSome } S₂ hc₂
    (by simp (disch := first | assumption | (apply Ne.symm; assumption)) [S₂,S₁])
    (by simpa (disch := first | assumption | (apply Ne.symm; assumption)) [S₂,S₁] using hw) (by
      intro k hk
      have hh := hz k (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
        rcases hk with rfl | rfl | rfl <;> simp)
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl
      all_goals simpa (disch := first | assumption | (apply Ne.symm; assumption)) [S₂,S₁] using hh) rfl
  let S₃ : Stacks T A := { S₂ with R := (trimAdvanceUpdate S₂.R count savedCount control savedControl acc []
    cs.reverse tail (gatherControls A ds).reverse (gatherControls A (ds.map (·-L))).reverse) }
  obtain ⟨v₄,hu₄,he₄⟩ := moveR_exec body acc dst ‹acc ≠ dst› id v₃ S₃
  let S₄ : Stacks T A := { S₃ with R := movedR S₃.R acc dst id (S₃.R acc) }
  obtain ⟨v₅,hu₅,he₅⟩ := moveR_exec body savedControl control ‹control ≠ savedControl›.symm id v₄ S₄
  let S₅ : Stacks T A := { S₄ with R := movedR S₄.R savedControl control id (S₄.R savedControl) }
  obtain ⟨v₆,hu₆,he₆⟩ := moveR_exec body savedCount count ‹count ≠ savedCount›.symm id v₅ S₅
  have hacc : (S₃.R acc).length = (ds.map (·-L)).sum+ds.length+d+1 := by
    simp (disch := first | assumption | (apply Ne.symm; assumption)) [S₃,S₂,S₁,trimAdvanceUpdate]
    omega
  have hcontrol : (S₄.R savedControl).length = ds.sum+ds.length+d+1 := by
    simp (disch := first | assumption | (apply Ne.symm; assumption)) [S₄,S₃,S₂,S₁,trimAdvanceUpdate,movedR]
    omega
  have hcount : (S₅.R savedCount).length = ds.length+1 := by
    simp (disch := first | assumption | (apply Ne.symm; assumption)) [S₅,S₄,S₃,S₂,S₁,trimAdvanceUpdate,movedR,hlen]
  refine ⟨v₆,_,hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans hu₁))),?_,
    (Exec.seq he₁' (Exec.seq (hpop ▸ Exec.act (body := body) (popPush count savedCount) _)
      (Exec.seq hp (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅ he₆)))))).cast rfl ?_⟩
  · rw [hacc,hcontrol,hcount]
    have hsum := sum_trimAdvances L ds hLd
    have ht : (ds.map (·-L)).sum ≤ ds.sum := by omega
    have hLsum : ds.length*L ≤ ds.sum := by omega
    nlinarith only [ht,hLsum]
  · have heffect : [count,savedCount,control,savedControl,acc].Nodup := by regs_nodup
    have hmid : S₂.R = trimAdvanceUpdate S.R count savedCount control savedControl acc
        cs [c] (gatherControls A ds++tail) (blank::List.replicate d tick) (blank::List.replicate d tick) := by
      funext k
      simp only [S₂,S₁,trimAdvanceUpdate,Function.update_apply,List.cons_append,List.nil_append]
      split_ifs <;> subst_vars <;> simp_all only [ne_eq,eq_self,not_false_eq_true,List.append_nil]
    have hbank : S₃.R = trimAdvanceUpdate S.R count savedCount control savedControl acc []
        (c::cs).reverse tail (gatherControls A (d::ds)).reverse
        (gatherControls A (d::ds.map (·-L))).reverse := by
      dsimp only [S₃]
      rw [hmid,trimAdvanceUpdate_comp heffect]
      simp only [gatherControls,List.reverse_cons,List.reverse_append,List.reverse_replicate,
        List.append_assoc,List.singleton_append]
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    dsimp only [S₅,S₄]
    rw [hbank]
    exact publicationControls_restore (by regs_nodup) S.R (c::cs)
      (gatherControls A (d::ds)) tail (gatherControls A (d::ds.map (·-L))) hc hs hzc hzs hza

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
