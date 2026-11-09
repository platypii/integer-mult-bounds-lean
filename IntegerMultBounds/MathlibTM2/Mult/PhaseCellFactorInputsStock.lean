module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorInputLoopStock

/-! Complete shifted factor inputs execute with one shared lookup reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

@[irreducible] def factorInputsWorkspace (q W N : ℕ) : ℕ :=
  2*(4*N+4)+(2*(4*N+5)+(N*((2*W+1)*(2*q+8))+factorSlidingStepWorkspace q W N (1+N)))

theorem factorInputs_exec_within {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hformat : ColumnFamilyFormat (2*q+8) columns) (hA : 4 ≤ A)
    (tail : List (Fin (A+4))) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hq : (S.R 119).length = q) (hW : (S.R 94).length = W) (hN : (S.R 116).length = B.card)
    (hcolumn : S.R 108 = []) (hrow : S.R 107 = [])
    (h105 : S.R 105 = []) (h106 : S.R 106 = [])
    (hsource : S.R 132 = bandTableWords A (2*q+8) B W columns 0++tail)
    (h0 : S.R 0 = []) (h111 : S.R 111 = []) (h112 : S.R 112 = [])
    (hfresh : ∀ k ∈ [(131 : Fin 154),134,135,136,137,138,151,152,153], S.R k = [])
    (hblank : ∀ r : Fin 154, 1 ≤ r.val → r.val < 7 → S.R r = []) (depth : ℕ) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ factorInputsCost q W B.card ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+factorInputsWorkspace q W B.card)
        depth factorInputs (mk v S) steps
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
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := factorInputLoop_exec_within (body := body) B q W 1 L depth columns hlen hformat hA
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
  let loopWork := L*((2*W+1)*(2*q+8))+factorSlidingStepWorkspace q W B.card (1+L)
  have hloop := he₃.mono (J := fun d z => mnSize z+d ≤ mnSize (mk v₂ S₂)+depth+loopWork)
    (by intro d z hz; dsimp only [loopWork]; omega)
  let output := cstream A (2*q+8) ((List.range' 1 L).flatMap (fun n => (List.range' n (2*W+1)).map (fun k => factorRankWord B W columns k (W+n))))++S.R 140
  let S₃ : Stacks 154 A := {S₁ with R := Function.update (Function.update S₁.R 107 [tick]) 140 output}
  have he₃' : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v₂ S₂)+depth+loopWork)
      depth factorInputLoop (mk v₂ S₂) m₃ (mk v₃ S₃) := by
    convert hloop using 1
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
  have hncopy : mnNativePushBound 2 (ucopy (P := P) (Q := Q) (A := A) (U := U) (116 : Fin 154) 111 135) := by
    simp [ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  have hncursor : mnNativePushBound 2 (factorInputCursor (P := P) (Q := Q) (A := A) (U := U)) := by
    simp [factorInputCursor,ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,
      whileR,peekR,mnNativePushBound,mnActPush]
  have ht₁ := mn_native_exec_within he₁' 2 hncopy depth _ (Nat.le_refl _)
  have ht₂ := mn_native_exec_within he₂ 2 hncursor depth _ (Nat.le_refl _)
  have ht₄ := mn_native_exec_within he₄' 0 (by
    simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]) depth
    (mnSize (mk v₂ S₂)+depth+loopWork)
    (by simpa only [Nat.zero_mul,Nat.add_zero] using he₃'.final)
  have ht₅ := mn_native_exec_within he₅ 0 (by
    simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]) depth
    (mnSize (mk v₂ S₂)+depth+loopWork)
    (by simpa only [Nat.zero_mul,Nat.add_zero] using ht₄.final)
  have ht := (mn_seq_within_add ht₁ (mn_seq_within_add ht₂
      (ExecWithin.seq he₃' (ExecWithin.seq ht₄ ht₅)))).mono
    (J := fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+factorInputsWorkspace q W B.card)
    (by intro d z hz; unfold factorInputsWorkspace; exact hz)
  refine ⟨v₅,(4*L+4)+((4*L+5)+(m₃+(4+(2*L+2)))),hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),
    Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_right hm₃ _) _) _,
    ht.cast (by rw [hlen111]) ?_⟩
  apply congrArg (mk v₅)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk111 : k = 111 <;> by_cases hk140 : k = 140 <;> simp [S₄,S₁,output,L,hk111,hk140,h111]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
