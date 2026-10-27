module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorInputLoop

/-! Generate all shifted update rows and release the starting-column and count controls. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

def factorInputCursor : Pr P 154 Q A U :=
  .seq (ucopy 111 107 135) (.act (.push (.rt 107) (fun _ => tick) .done))

theorem factorInputCursor_exec (L : ℕ) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hcount : (S.R 111).length = L) (h107 : S.R 107 = []) (h135 : S.R 135 = []) :
    ∃ v', v'.user = v.user ∧ Exec body factorInputCursor (mk v S) (4*L+5)
      (mk v' {S with R := Function.update S.R 107 (List.replicate (L+1) tick)}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec body (a := 111) (b := 107) (t := 135) (by decide) (by decide) (by decide) v S h135
  let S₁ : Stacks 154 A := {S with R := Function.update S.R 107 (List.replicate L tick)}
  have he₁' : Exec body (ucopy 111 107 135) (mk v S) (4*L+4) (mk v₁ S₁) := by simpa [S₁,hcount,h107] using he₁
  have he₂ := Exec.act (body := body) (.push (.rt 107) (fun _ => tick) .done) (mk v₁ S₁)
  refine ⟨v₁,hu₁,(Exec.seq he₁' he₂).cast (by omega) ?_⟩
  simp [S₁,Action.run,update_rt,List.replicate_succ]

def factorInputs : Pr P 154 Q A U :=
  .seq (ucopy 116 111 135) (.seq factorInputCursor (.seq factorInputLoop (.seq (uclear 107) (uclear 111))))

def factorInputsCost (q W N : ℕ) : ℕ :=
  (4*N+4)+((4*N+5)+(factorInputLoopCost q W N 1 N+(4+(2*N+2))))

theorem factorInputs_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hformat : ColumnFamilyFormat (2*q+8) columns) (hA : 4 ≤ A)
    (tail : List (Fin (A+4))) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hq : (S.R 119).length = q) (hW : (S.R 94).length = W) (hN : (S.R 116).length = B.card)
    (hcolumn : S.R 108 = []) (hrow : S.R 107 = [])
    (h105 : S.R 105 = []) (h106 : S.R 106 = [])
    (hsource : S.R 132 = bandTableWords A (2*q+8) B W columns 0++tail)
    (h0 : S.R 0 = []) (h111 : S.R 111 = []) (h112 : S.R 112 = [])
    (hfresh : ∀ k ∈ [(131 : Fin 154),134,135,136,137,138,151,152,153], S.R k = [])
    (hblank : ∀ r : Fin 154, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ factorInputsCost q W B.card ∧
      Exec body factorInputs (mk v S) steps
        (mk v' {S with R := (Function.update S.R 140
          (cstream A (2*q+8) ((List.range' 1 B.card).flatMap (fun n => (List.range' n (2*W+1)).map (fun k => factorRankWord B W columns k (W+n))))++S.R 140))}) := by
  let L := B.card
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec body (a := 116) (b := 111) (t := 135)
    (by decide) (by decide) (by decide) v S (hfresh 135 (by simp))
  let S₁ : Stacks 154 A := {S with R := Function.update S.R 111 (List.replicate L tick)}
  have he₁' : Exec body (ucopy 116 111 135) (mk v S) (4*L+4) (mk v₁ S₁) := by simpa [S₁,L,hN,h111] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := factorInputCursor_exec (body := body) L v₁ S₁
    (by simp [S₁]) (by simpa [S₁] using hrow) (by simpa [S₁] using hfresh 135 (by simp))
  let S₂ : Stacks 154 A := {S₁ with R := Function.update S₁.R 107 (List.replicate (L+1) tick)}
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := factorInputLoop_exec (body := body) B q W 1 L columns hlen hformat hA
    tail v₂ S₂ (by simpa [S₂,S₁] using hq) (by simpa [S₂,S₁] using hW) (by simpa [S₂,S₁] using hN)
    (by simp [S₂,S₁,Nat.add_comm]) (by simpa [S₂,S₁] using hcolumn)
    (by simpa [S₂,S₁] using h105) (by simpa [S₂,S₁] using h106) (by simp [S₂,S₁])
    (by simpa [S₂,S₁] using hsource) (by simpa [S₂,S₁] using h0) (by simpa [S₂,S₁] using h112)
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [S₂,S₁] using hfresh _ (by simp)) (by
      intro r hr1 hr7
      have hr111 : r ≠ 111 := by omega
      have hr107 : r ≠ 107 := by omega
      simpa [S₂,S₁,hr111,hr107] using hblank r hr1 hr7)
  let output := cstream A (2*q+8) ((List.range' 1 L).flatMap (fun n => (List.range' n (2*W+1)).map (fun k => factorRankWord B W columns k (W+n))))++S.R 140
  let S₃ : Stacks 154 A := {S₁ with R := Function.update (Function.update S₁.R 107 [tick]) 140 output}
  have he₃' : Exec body factorInputLoop (mk v₂ S₂) m₃ (mk v₃ S₃) := by
    convert he₃ using 1
    apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk107 : k = 107 <;> by_cases hk140 : k = 140 <;> simp [S₃,S₂,S₁,output,hk107,hk140]
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec body 107 v₃ S₃
  let S₄ : Stacks 154 A := {S₁ with R := Function.update S₁.R 140 output}
  have he₄' : Exec body (uclear 107) (mk v₃ S₃) 4 (mk v₄ S₄) := by
    convert he₄ using 1
    · simp [S₃]
    · apply congrArg (mk v₄)
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      by_cases hk107 : k = 107 <;> by_cases hk140 : k = 140 <;> simp [S₄,S₃,S₁,hk107,hk140,hrow]
  obtain ⟨v₅,hu₅,he₅⟩ := uclear_exec body 111 v₄ S₄
  have hlen111 : (S₄.R 111).length = L := by simp [S₄,S₁]
  refine ⟨v₅,(4*L+4)+((4*L+5)+(m₃+(4+(2*L+2)))),hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),
    Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_right hm₃ _) _) _,
    (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃' (Exec.seq he₄' he₅)))).cast (by rw [hlen111]) ?_⟩
  apply congrArg (mk v₅)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk111 : k = 111 <;> by_cases hk140 : k = 140 <;> simp [S₄,S₁,output,L,hk111,hk140,h111]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
