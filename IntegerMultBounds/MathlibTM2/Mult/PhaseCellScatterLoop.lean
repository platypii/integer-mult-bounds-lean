module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScatterPacket
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScatterData

/-! A fixed tape loop publishes disjoint windows in one forward sweep. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

def scatterLoopBody (control savedControl gap window src dst acc trash tmp : Fin T) : Pr P T Q A U :=
  .seq (scatterPacket control savedControl gap window src dst acc trash tmp) (.act (peekR control))

theorem scatterLoop_exec {control savedControl gap window src dst acc trash tmp : Fin T}
    (hreg : [control,savedControl,gap,window,src,dst,acc,trash,tmp].Nodup)
    (L : ℕ) (ds : List ℕ) (E X : List (Fin (A+4)))
    (hf : ScatterFits L E ds) (hx : ds.length*L ≤ X.length)
    (v : HS T Q A U) (S : Stacks T A)
    (hc : S.R control = gatherControls A ds) (hdst : S.R dst = E) (hsrc : S.R src = X)
    (hw : (S.R window).length = L)
    (hclean : ∀ k ∈ [gap,trash,tmp], S.R k = [])
    (hflag : v.flag = (gatherControls A ds).head?.isSome) :
    ∃ v', v'.user = v.user ∧
      Exec body (.loop (·.flag) (scatterLoopBody control savedControl gap window src dst acc trash tmp))
        (mk v S) (ds.length*(10*L+21)+8*ds.sum+1)
        (mk v' { S with R := (scatterUpdate S.R control savedControl src dst acc []
          (gatherControls A ds).reverse (X.drop (ds.length*L)) (E.drop (scatterVolume L ds))
          (scatterPrefix L E X ds).reverse) }) := by
  have hr := hreg
  regs_ne hr
  have heffect : [control,savedControl,src,dst,acc].Nodup := by regs_nodup
  induction ds generalizing E X v S with
  | nil =>
    have he := Exec.loop_false (body := body)
      (p := scatterLoopBody control savedControl gap window src dst acc trash tmp)
      (s := mk v S) (by simpa [gatherControls] using hflag)
    refine ⟨v,rfl,he.cast (by simp) ?_⟩
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    simp only [scatterUpdate,gatherControls,scatterPrefix,List.length_nil,Nat.zero_mul,
      scatterVolume_nil,List.drop_zero,List.reverse_nil,List.nil_append,Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all only [ne_eq,eq_self,not_false_eq_true,gatherControls]
  | cons d ds ih =>
    have hL : L ≤ X.length := by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at hx
      omega
    have hrest : ds.length*L ≤ (X.drop L).length := by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at hx
      simp only [List.length_drop]; omega
    have hd : d ≤ E.length := by have := hf.1; omega
    have hfit : L ≤ (E.drop d).length := by
      have := hf.1
      simp only [List.length_drop]; omega
    obtain ⟨v₁,hu₁,he₁⟩ := scatterPacket_exec (body := body) hreg d (gatherControls A ds)
      (E.take d) ((E.drop d).take L) ((E.drop d).drop L) (X.take L) (X.drop L) v S
      hc (by simpa [List.append_assoc] using hdst) (by simpa using hsrc)
      (by simp [List.length_take,Nat.min_eq_left hd])
      (by simpa [List.length_take,Nat.min_eq_left hL] using hw)
      (by rw [List.length_take,Nat.min_eq_left hfit,List.length_take,Nat.min_eq_left hL])
      (hclean gap (by simp)) (hclean trash (by simp)) (hclean tmp (by simp))
    let S₁ : Stacks T A := { S with R := (scatterUpdate S.R control savedControl src dst acc
      (gatherControls A ds) (blank :: List.replicate d tick) (X.drop L) (E.drop (d+L))
      ((X.take L).reverse++(E.take d).reverse)) }
    have he₁' : Exec body (scatterPacket control savedControl gap window src dst acc trash tmp)
        (mk v S) (8*d+10*L+19) (mk v₁ S₁) := by
      simpa only [S₁,List.length_take,Nat.min_eq_left hL,List.drop_drop] using he₁
    have stable (k : Fin T) (hkc : k ≠ control) (hksc : k ≠ savedControl)
        (hks : k ≠ src) (hkd : k ≠ dst) (hka : k ≠ acc) : S₁.R k = S.R k := by
      simp [S₁,scatterUpdate,hkc,hksc,hks,hkd,hka]
    have hclean₁ : ∀ k ∈ [gap,trash,tmp], S₁.R k = [] := by
      intro k hk
      have hz := hclean k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl
      all_goals rw [stable _ (by first | assumption | (apply Ne.symm; assumption))
        (by first | assumption | (apply Ne.symm; assumption))
        (by first | assumption | (apply Ne.symm; assumption))
        (by first | assumption | (apply Ne.symm; assumption))
        (by first | assumption | (apply Ne.symm; assumption))]; exact hz
    have hc₁ : S₁.R control = gatherControls A ds := by
      simp (disch := first | assumption | (apply Ne.symm; assumption)) [S₁,scatterUpdate]
    have hd₁ : S₁.R dst = E.drop (d+L) := by
      simp (disch := first | assumption | (apply Ne.symm; assumption)) [S₁,scatterUpdate]
    have hs₁ : S₁.R src = X.drop L := by
      simp (disch := first | assumption | (apply Ne.symm; assumption)) [S₁,scatterUpdate]
    have hp := Exec.act (body := body) (peekR control) (mk v₁ S₁)
    rw [peekR_run,hc₁] at hp
    obtain ⟨v₂,hu₂,he₂⟩ := ih (E.drop (d+L)) (X.drop L) hf.2 hrest
      { v₁ with flag := (gatherControls A ds).head?.isSome } S₁ hc₁ hd₁ hs₁
      (by rw [stable _ ‹control ≠ window›.symm ‹savedControl ≠ window›.symm
        ‹window ≠ src› ‹window ≠ dst› ‹window ≠ acc›]; exact hw)
      hclean₁ rfl
    have hstep : Exec body (scatterLoopBody control savedControl gap window src dst acc trash tmp)
        (mk v S) (8*d+10*L+20)
        (mk { v₁ with flag := (gatherControls A ds).head?.isSome } S₁) := by
      exact (Exec.seq he₁' hp).cast (by omega) rfl
    refine ⟨v₂,hu₂.trans hu₁,(Exec.loop_true ?_ hstep he₂).cast ?_ ?_⟩
    · simpa [gatherControls] using hflag
    · simp only [List.length_cons,List.sum_cons]; ring
    · congr 1
      ext1
      · rfl
      · rfl
      · rfl
      change scatterUpdate (scatterUpdate S.R control savedControl src dst acc _ _ _ _ _)
        control savedControl src dst acc _ _ _ _ _ = _
      rw [scatterUpdate_comp heffect]
      simp only [gatherControls,scatterPrefix,scatterVolume_cons,List.length_cons,Nat.add_mul,
        Nat.one_mul,List.drop_drop,List.reverse_append,List.reverse_cons,List.reverse_replicate,
        List.append_assoc,List.singleton_append]
      simp only [Nat.add_assoc,Nat.add_comm]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
