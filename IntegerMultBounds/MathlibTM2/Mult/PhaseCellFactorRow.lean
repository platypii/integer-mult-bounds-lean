module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorRowLoop

/-! Generate a complete fixed-width factor row and restore its borrowed cursor and count workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

def factorRowCount : Pr P 154 Q A U := .seq (umul 2 94 105 135) (.act (.push (.rt 105) (fun _ => tick) .done))

theorem factorRowCount_exec (W : ℕ) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hW : (S.R 94).length = W) (h105 : S.R 105 = []) (h135 : S.R 135 = []) :
    ∃ v', v'.user = v.user ∧ Exec body factorRowCount (mk v S) (4*W+5)
      (mk v' {S with R := Function.update S.R 105 (List.replicate (2*W+1) tick)}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := umul_exec body 2 (a := 94) (b := 105) (t := 135) (by decide) (by decide) (by decide) v S h135
  let S₁ : Stacks 154 A := {S with R := Function.update S.R 105 (List.replicate (2*W) tick)}
  have he₁' : Exec body (umul 2 94 105 135) (mk v S) (4*W+4) (mk v₁ S₁) := by simpa [S₁,hW,h105] using he₁
  have he₂ := Exec.act (body := body) (.push (.rt 105) (fun _ => tick) .done) (mk v₁ S₁)
  refine ⟨v₁,hu₁,(Exec.seq he₁' he₂).cast (by omega) ?_⟩
  simp [S₁,Action.run,update_rt,List.replicate_succ]

def factorRow : Pr P 154 Q A U :=
  .seq factorRowCount (.seq (ucopy 105 107 135) (.seq factorRowLoop (uclear 105)))

def factorRowCost (q W N start m : ℕ) : ℕ :=
  let L := 2*W+1
  (4*W+5)+((4*L+4)+(factorRowLoopCost q W N start L m+(2*L+2)))

theorem factorRow_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q W start m : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hformat : ColumnFamilyFormat (2*q+8) columns) (hA : 4 ≤ A)
    (tail : List (Fin (A+4))) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hq : (S.R 119).length = q) (hW : (S.R 94).length = W) (hN : (S.R 116).length = B.card)
    (hcolumn : (S.R 107).length = start) (hrow : (S.R 108).length = m)
    (hsource : S.R 132 = bandTableWords A (2*q+8) B W columns 0++tail)
    (h0 : S.R 0 = []) (h105 : S.R 105 = []) (h106 : S.R 106 = [])
    (hfresh : ∀ k ∈ [(131 : Fin 154),134,135,136,137,138,151,152,153], S.R k = [])
    (hblank : ∀ r : Fin 154, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ factorRowCost q W B.card start m ∧
      Exec body factorRow (mk v S) steps
        (mk v' {S with R := (Function.update S.R 140
          (cstream A (2*q+8) ((List.range' start (2*W+1)).map (fun n => factorRankWord B W columns n m))++S.R 140))}) := by
  let L := 2*W+1
  obtain ⟨v₁,hu₁,he₁⟩ := factorRowCount_exec (body := body) W v S hW h105 (hfresh 135 (by simp))
  let S₁ : Stacks 154 A := {S with R := Function.update S.R 105 (List.replicate L tick)}
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec body (a := 105) (b := 107) (t := 135)
    (by decide) (by decide) (by decide) v₁ S₁ (by simpa [S₁] using hfresh 135 (by simp))
  let S₂ : Stacks 154 A := {S₁ with R := Function.update S₁.R 107 (List.replicate L tick++S.R 107)}
  have he₂' : Exec body (ucopy 105 107 135) (mk v₁ S₁) (4*L+4) (mk v₂ S₂) := by simpa [S₂,S₁] using he₂
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := factorRowLoop_exec (body := body) B q W start L m columns hlen hformat hA
    tail v₂ S₂ (by simpa [S₂,S₁] using hq) (by simpa [S₂,S₁] using hW) (by simpa [S₂,S₁] using hN)
    (by simp [S₂,S₁,hcolumn,Nat.add_comm]) (by simpa [S₂,S₁] using hrow) (by simp [S₂,S₁])
    (by simpa [S₂,S₁] using hsource) (by simpa [S₂,S₁] using h0) (by simpa [S₂,S₁] using h106)
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [S₂,S₁] using hfresh _ (by simp)) (by
      intro r hr1 hr7
      have hr105 : r ≠ 105 := by omega
      have hr107 : r ≠ 107 := by omega
      simpa [S₂,S₁,hr105,hr107] using hblank r hr1 hr7)
  let output := cstream A (2*q+8) ((List.range' start L).map (fun n => factorRankWord B W columns n m))++S.R 140
  let S₃ : Stacks 154 A := {S₁ with R := Function.update S₁.R 140 output}
  have he₃' : Exec body factorRowLoop (mk v₂ S₂) m₃ (mk v₃ S₃) := by
    convert he₃ using 1
    apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk107 : k = 107 <;> by_cases hk140 : k = 140 <;> simp [S₃,S₂,S₁,output,hk107,hk140]
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec body 105 v₃ S₃
  have hlen105 : (S₃.R 105).length = L := by simp [S₃,S₁]
  refine ⟨v₄,(4*W+5)+((4*L+4)+(m₃+(2*L+2))),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),
    Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_right hm₃ _) _) _,
    (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃' he₄))).cast (by rw [hlen105]) ?_⟩
  apply congrArg (mk v₄)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk105 : k = 105 <;> by_cases hk140 : k = 140 <;> simp [S₃,S₁,output,L,hk105,hk140,h105]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
