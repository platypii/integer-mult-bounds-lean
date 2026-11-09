module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorWindow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorWindowLoopStock

/-! Complete factor-window construction shares a reserve across both nested scans. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

@[irreducible] def factorWindowWorkspace (q W N : ℕ) : ℕ :=
  let L := W+1
  2*(4*W+5)+(2*(4*L+4)+(L*((2*W+1)*(2*q+8))+factorRowWorkspace q W N 0 L))

theorem factorWindow_exec_within {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hformat : ColumnFamilyFormat (2*q+8) columns) (hA : 4 ≤ A)
    (tail : List (Fin (A+4))) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hq : (S.R 119).length = q) (hW : (S.R 94).length = W) (hN : (S.R 116).length = B.card)
    (hcolumn : S.R 107 = []) (hrow : S.R 108 = [])
    (h105 : S.R 105 = []) (h106 : S.R 106 = [])
    (hsource : S.R 132 = bandTableWords A (2*q+8) B W columns 0++tail)
    (h0 : S.R 0 = []) (h111 : S.R 111 = []) (h112 : S.R 112 = [])
    (hfresh : ∀ k ∈ [(131 : Fin 154),134,135,136,137,138,151,152,153], S.R k = [])
    (hblank : ∀ r : Fin 154, 1 ≤ r.val → r.val < 7 → S.R r = []) (depth : ℕ) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ factorWindowCost q W B.card ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+factorWindowWorkspace q W B.card)
        depth factorWindow (mk v S) steps
        (mk v' {S with R := (Function.update S.R 140
          (cstream A (2*q+8) ((List.range' 0 (W+1)).flatMap (fun m => (List.range' 0 (2*W+1)).map (fun n => factorRankWord B W columns n m)))++S.R 140))}) := by
  let L := W+1
  obtain ⟨v₁,hu₁,he₁⟩ := factorWindowCount_exec (body := body) W v S hW h111 (hfresh 135 (by simp))
  let S₁ : Stacks 154 A := {S with R := Function.update S.R 111 (List.replicate L tick)}
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec body (a := 111) (b := 108) (t := 135)
    (by decide) (by decide) (by decide) v₁ S₁ (by simpa [S₁] using hfresh 135 (by simp))
  let S₂ : Stacks 154 A := {S₁ with R := Function.update S₁.R 108 (List.replicate L tick++S.R 108)}
  have he₂' : Exec body (ucopy 111 108 135) (mk v₁ S₁) (4*L+4) (mk v₂ S₂) := by simpa [S₂,S₁] using he₂
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := factorWindowLoop_exec_within (body := body) B q W 0 L depth columns hlen hformat hA
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
  have hloop := he₃.mono (J := fun d z => mnSize z+d ≤ mnSize (mk v₂ S₂)+depth+
    (L*((2*W+1)*(2*q+8))+factorRowWorkspace q W B.card 0 L)) (by intro d z hz; simp only [Nat.zero_add] at hz; omega)
  let output := cstream A (2*q+8) ((List.range' 0 L).flatMap (fun m => (List.range' 0 (2*W+1)).map (fun n => factorRankWord B W columns n m)))++S.R 140
  let S₃ : Stacks 154 A := {S₁ with R := Function.update S₁.R 140 output}
  have he₃' : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v₂ S₂)+depth+
      (L*((2*W+1)*(2*q+8))+factorRowWorkspace q W B.card 0 L)) depth factorWindowLoop (mk v₂ S₂) m₃ (mk v₃ S₃) := by
    convert hloop using 1
    apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk108 : k = 108 <;> by_cases hk140 : k = 140 <;> simp [S₃,S₂,S₁,output,hk108,hk140,hrow]
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec body 111 v₃ S₃
  have hlen111 : (S₃.R 111).length = L := by simp [S₃,S₁]
  have hncount : mnNativePushBound 2 (factorWindowCount (P := P) (Q := Q) (A := A) (U := U)) := by
    simp [factorWindowCount,ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,
      whileR,peekR,mnNativePushBound,mnActPush]
  have hncopy : mnNativePushBound 2 (ucopy (P := P) (Q := Q) (A := A) (U := U) (111 : Fin 154) 108 135) := by
    simp [ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  have ht₁ := mn_native_exec_within he₁ 2 hncount depth _ (Nat.le_refl _)
  have ht₂ := mn_native_exec_within he₂' 2 hncopy depth _ (Nat.le_refl _)
  have ht₄ := mn_native_exec_within he₄ 0 (by
    simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]) depth
    (mnSize (mk v₂ S₂)+depth+(L*((2*W+1)*(2*q+8))+factorRowWorkspace q W B.card 0 L))
    (by simpa only [Nat.zero_mul,Nat.add_zero] using he₃'.final)
  have ht := (mn_seq_within_add ht₁ (mn_seq_within_add ht₂ (ExecWithin.seq he₃' ht₄))).mono
    (J := fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+factorWindowWorkspace q W B.card)
    (by intro d z hz; unfold factorWindowWorkspace; exact hz)
  refine ⟨v₄,(4*W+5)+((4*L+4)+(m₃+(2*L+2))),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),
    Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_right hm₃ _) _) _,
    ht.cast (by rw [hlen111]) ?_⟩
  apply congrArg (mk v₄)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk111 : k = 111 <;> by_cases hk140 : k = 140 <;> simp [S₃,S₁,output,L,hk111,hk140,h111]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
