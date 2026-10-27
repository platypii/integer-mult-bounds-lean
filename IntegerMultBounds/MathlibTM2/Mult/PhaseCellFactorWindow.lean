module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorWindowLoop

/-! Generate the complete initial factor window and release its row and count controls. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

def factorWindowCount : Pr P 154 Q A U := .seq (ucopy 94 111 135) (.act (.push (.rt 111) (fun _ => tick) .done))

theorem factorWindowCount_exec (W : ℕ) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hW : (S.R 94).length = W) (h111 : S.R 111 = []) (h135 : S.R 135 = []) :
    ∃ v', v'.user = v.user ∧ Exec body factorWindowCount (mk v S) (4*W+5)
      (mk v' {S with R := Function.update S.R 111 (List.replicate (W+1) tick)}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec body (a := 94) (b := 111) (t := 135) (by decide) (by decide) (by decide) v S h135
  let S₁ : Stacks 154 A := {S with R := Function.update S.R 111 (List.replicate (W) tick)}
  have he₁' : Exec body (ucopy 94 111 135) (mk v S) (4*W+4) (mk v₁ S₁) := by simpa [S₁,hW,h111] using he₁
  have he₂ := Exec.act (body := body) (.push (.rt 111) (fun _ => tick) .done) (mk v₁ S₁)
  refine ⟨v₁,hu₁,(Exec.seq he₁' he₂).cast (by omega) ?_⟩
  simp [S₁,Action.run,update_rt,List.replicate_succ]

def factorWindow : Pr P 154 Q A U :=
  .seq factorWindowCount (.seq (ucopy 111 108 135) (.seq factorWindowLoop (uclear 111)))

def factorWindowCost (q W N : ℕ) : ℕ :=
  let L := W+1
  (4*W+5)+((4*L+4)+(factorWindowLoopCost q W N 0 L+(2*L+2)))

theorem factorWindow_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hformat : ColumnFamilyFormat (2*q+8) columns) (hA : 4 ≤ A)
    (tail : List (Fin (A+4))) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hq : (S.R 119).length = q) (hW : (S.R 94).length = W) (hN : (S.R 116).length = B.card)
    (hcolumn : S.R 107 = []) (hrow : S.R 108 = [])
    (h105 : S.R 105 = []) (h106 : S.R 106 = [])
    (hsource : S.R 132 = bandTableWords A (2*q+8) B W columns 0++tail)
    (h0 : S.R 0 = []) (h111 : S.R 111 = []) (h112 : S.R 112 = [])
    (hfresh : ∀ k ∈ [(131 : Fin 154),134,135,136,137,138,151,152,153], S.R k = [])
    (hblank : ∀ r : Fin 154, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ factorWindowCost q W B.card ∧
      Exec body factorWindow (mk v S) steps
        (mk v' {S with R := (Function.update S.R 140
          (cstream A (2*q+8) ((List.range' 0 (W+1)).flatMap (fun m => (List.range' 0 (2*W+1)).map (fun n => factorRankWord B W columns n m)))++S.R 140))}) := by
  let L := W+1
  obtain ⟨v₁,hu₁,he₁⟩ := factorWindowCount_exec (body := body) W v S hW h111 (hfresh 135 (by simp))
  let S₁ : Stacks 154 A := {S with R := Function.update S.R 111 (List.replicate L tick)}
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec body (a := 111) (b := 108) (t := 135)
    (by decide) (by decide) (by decide) v₁ S₁ (by simpa [S₁] using hfresh 135 (by simp))
  let S₂ : Stacks 154 A := {S₁ with R := Function.update S₁.R 108 (List.replicate L tick++S.R 108)}
  have he₂' : Exec body (ucopy 111 108 135) (mk v₁ S₁) (4*L+4) (mk v₂ S₂) := by simpa [S₂,S₁] using he₂
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := factorWindowLoop_exec (body := body) B q W 0 L columns hlen hformat hA
    tail v₂ S₂ (by simpa [S₂,S₁] using hq) (by simpa [S₂,S₁] using hW) (by simpa [S₂,S₁] using hN)
    (by simp [S₂,S₁,hrow]) (by simpa [S₂,S₁] using hcolumn)
    (by simpa [S₂,S₁] using h105) (by simpa [S₂,S₁] using h106) (by simp [S₂,S₁])
    (by simpa [S₂,S₁] using hsource) (by simpa [S₂,S₁] using h0) (by simpa [S₂,S₁] using h112)
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [S₂,S₁] using hfresh _ (by simp)) (by
      intro r hr1 hr7
      have hr111 : r ≠ 111 := by omega
      have hr108 : r ≠ 108 := by omega
      simpa [S₂,S₁,hr111,hr108] using hblank r hr1 hr7)
  let output := cstream A (2*q+8) ((List.range' 0 L).flatMap (fun m => (List.range' 0 (2*W+1)).map (fun n => factorRankWord B W columns n m)))++S.R 140
  let S₃ : Stacks 154 A := {S₁ with R := Function.update S₁.R 140 output}
  have he₃' : Exec body factorWindowLoop (mk v₂ S₂) m₃ (mk v₃ S₃) := by
    convert he₃ using 1
    apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk108 : k = 108 <;> by_cases hk140 : k = 140 <;> simp [S₃,S₂,S₁,output,hk108,hk140,hrow]
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec body 111 v₃ S₃
  have hlen111 : (S₃.R 111).length = L := by simp [S₃,S₁]
  refine ⟨v₄,(4*W+5)+((4*L+4)+(m₃+(2*L+2))),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),
    Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_right hm₃ _) _) _,
    (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃' he₄))).cast (by rw [hlen111]) ?_⟩
  apply congrArg (mk v₄)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk111 : k = 111 <;> by_cases hk140 : k = 140 <;> simp [S₃,S₁,output,L,hk111,hk140,h111]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
