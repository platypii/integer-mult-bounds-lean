module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorSlidingStep
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorRowWorkspaceBound

/-! Shifted update rows retain the shared row reserve through control setup and cleanup. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

@[irreducible] def factorSlidingStepWorkspace (q W N n : ℕ) : ℕ :=
  2*(4*n+4)+(2*(4*W+4)+factorRowWorkspace q W N n (W+n))

theorem factorSlidingStepWorkspace_mono (q W N n m : ℕ) (hn : n ≤ m) :
    factorSlidingStepWorkspace q W N n ≤ factorSlidingStepWorkspace q W N m := by
  have hr := factorRowWorkspace_mono q W N n m (W+n) (W+m) hn (Nat.add_le_add_left hn W)
  unfold factorSlidingStepWorkspace
  omega

theorem factorSlidingStep_exec_within {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q W n : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hformat : ColumnFamilyFormat (2*q+8) columns) (hA : 4 ≤ A)
    (tail : List (Fin (A+4))) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hq : (S.R 119).length = q) (hW : (S.R 94).length = W) (hN : (S.R 116).length = B.card)
    (hcolumn : (S.R 107).length = n+1) (hrow : S.R 108 = [])
    (h105 : S.R 105 = []) (h106 : S.R 106 = [])
    (hsource : S.R 132 = bandTableWords A (2*q+8) B W columns 0++tail) (h0 : S.R 0 = [])
    (hfresh : ∀ k ∈ [(131 : Fin 154),134,135,136,137,138,151,152,153], S.R k = [])
    (hblank : ∀ r : Fin 154, 1 ≤ r.val → r.val < 7 → S.R r = []) (depth : ℕ) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ factorSlidingStepCost q W B.card n ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+factorSlidingStepWorkspace q W B.card n)
        depth factorSlidingStep (mk v S) steps
        (mk v' {S with R := (Function.update (Function.update S.R 107 (S.R 107).tail) 140
          (cstream A (2*q+8) ((List.range' n (2*W+1)).map (fun k => factorRankWord B W columns k (W+n)))++S.R 140))}) := by
  let S₁ : Stacks 154 A := {S with R := Function.update S.R 107 (S.R 107).tail}
  have he₁ : Exec body (.act (dropTop 107 .done)) (mk v S) 1 (mk v S₁) := by
    simpa [S₁,dropTop,Action.run,update_rt] using Exec.act (body := body) (dropTop 107 .done) (mk v S)
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec body (a := 107) (b := 108) (t := 135)
    (by decide) (by decide) (by decide) v S₁ (by simpa [S₁] using hfresh 135 (by simp))
  let S₂ : Stacks 154 A := {S₁ with R := Function.update S₁.R 108 (List.replicate n tick)}
  have he₂' : Exec body (ucopy 107 108 135) (mk v S₁) (4*n+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,hcolumn,hrow] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := ucopy_exec body (a := 94) (b := 108) (t := 135)
    (by decide) (by decide) (by decide) v₂ S₂ (by simpa [S₂,S₁] using hfresh 135 (by simp))
  let S₃ : Stacks 154 A := {S₂ with R := Function.update S₂.R 108 (List.replicate (W+n) tick)}
  have he₃' : Exec body (ucopy 94 108 135) (mk v₂ S₂) (4*W+4) (mk v₃ S₃) := by
    simpa [S₃,S₂,S₁,hW,List.replicate_append_replicate] using he₃
  obtain ⟨v₄,steps,hu₄,hs,he₄⟩ := factorRow_exec_within (body := body) B q W n (W+n) columns hlen hformat hA tail v₃ S₃
    (by simpa [S₃,S₂,S₁] using hq) (by simpa [S₃,S₂,S₁] using hW) (by simpa [S₃,S₂,S₁] using hN)
    (by simp [S₃,S₂,S₁,hcolumn]) (by simp [S₃]) (by simpa [S₃,S₂,S₁] using hsource)
    (by simpa [S₃,S₂,S₁] using h0) (by simpa [S₃,S₂,S₁] using h105) (by simpa [S₃,S₂,S₁] using h106)
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [S₃,S₂,S₁] using hfresh _ (by simp)) (by
      intro r hr1 hr7
      have hr107 : r ≠ 107 := by omega
      have hr108 : r ≠ 108 := by omega
      simpa [S₃,S₂,S₁,hr107,hr108] using hblank r hr1 hr7) depth
  let output := cstream A (2*q+8) ((List.range' n (2*W+1)).map (fun k => factorRankWord B W columns k (W+n)))++S.R 140
  let S₄ : Stacks 154 A := {S₃ with R := Function.update S₃.R 140 output}
  have he₄' : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v₃ S₃)+depth+
      factorRowWorkspace q W B.card n (W+n)) depth factorRow (mk v₃ S₃) steps (mk v₄ S₄) := by
    simpa [S₄,S₃,S₂,S₁,output] using he₄
  obtain ⟨v₅,hu₅,he₅⟩ := uclear_exec body 108 v₄ S₄
  have h108 : (S₄.R 108).length = W+n := by simp [S₄,S₃]
  have hncopy (src : Fin 154) : mnNativePushBound 2 (ucopy (P := P) (Q := Q) (A := A) (U := U) src 108 135) := by
    simp [ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  have ht₁ := mn_native_exec_within he₁ 0 (by simp [dropTop,mnNativePushBound,mnActPush]) depth _ (Nat.le_refl _)
  have ht₂ := mn_native_exec_within he₂' 2 (hncopy 107) depth _ (Nat.le_refl _)
  have ht₃ := mn_native_exec_within he₃' 2 (hncopy 94) depth _ (Nat.le_refl _)
  have ht₅ := mn_native_exec_within he₅ 0 (by
    simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]) depth
    (mnSize (mk v₃ S₃)+depth+factorRowWorkspace q W B.card n (W+n))
    (by simpa only [Nat.zero_mul,Nat.add_zero] using he₄'.final)
  have ht := (mn_seq_within_add ht₁ (mn_seq_within_add ht₂
    (mn_seq_within_add ht₃ (ExecWithin.seq he₄' ht₅)))).mono
    (J := fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+factorSlidingStepWorkspace q W B.card n)
    (by intro d z hz; unfold factorSlidingStepWorkspace; simpa only [Nat.zero_mul,Nat.zero_add] using hz)
  refine ⟨v₅,1+((4*n+4)+((4*W+4)+(steps+(2*(W+n)+2)))),hu₅.trans (hu₄.trans (hu₃.trans hu₂)),?_,?_⟩
  · exact Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_right hs _) _) _) _
  · apply ht.cast (by rw [h108])
    apply congrArg (mk v₅)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk107 : k = 107 <;> by_cases hk108 : k = 108 <;> by_cases hk140 : k = 140 <;>
      simp [S₄,S₃,S₂,S₁,output,hk107,hk108,hk140,hrow]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
