module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundaryRhsFold
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRhsMaskSelection

/-! One ordered RHS scan and the canonical fold consume an owned generated boundary mask. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 148 Q A U}

def maskedBoundaryRhs : Pr P 148 Q A U :=
  .seq (gatherRecords 110 139 94 106 0 1 2 143 0 pairRe)
    (.seq preparedBoundaryRhsFold (uclear 139))

theorem maskedBoundaryRhs_exec {s t : ℕ} [NeZero s] (hst : s < t) (hA : 4 ≤ A)
    (band a b : ℕ) (hb : b ≤ s) (C : ZMod s → GaussianInt) (w : ℕ)
    (tail : List (Fin (A+4))) (v : HS 148 Q A U) (S : Stacks 148 A)
    (hsrc : S.R 110 = cstream A w (chirpLine s C)++tail)
    (hmask : S.R 139 = couplingSourceMaskSymbols true A s t band a b)
    (hw : (S.R 94).length = w) (hcount : (S.R 116).length = (haloBoundary s t band a b).card)
    (h143 : S.R 143 = []) (h106 : S.R 106 = [])
    (hblank : ∀ r : Fin 148, r.val < 77 → S.R r = []) (hleft : ∀ r, S.L r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 600*(s+1)*(w+1) ∧
      Exec body maskedBoundaryRhs (mk v S) m
        (mk v' {S with R := Function.update (Function.update S.R 139 []) 143 (cstream A w ((bFoldOrder s (haloBoundary s t band a b)).map C))}) := by
  let B := haloBoundary s t band a b
  let ordered := cstream A w ((bOrder s B).map C)
  let folded := cstream A w ((bFoldOrder s B).map C)
  let S₁ : Stacks 148 A := {S with R := Function.update S.R 143 ordered}
  let S₂ : Stacks 148 A := {S with R := Function.update S.R 143 folded}
  let S₃ : Stacks 148 A := {S with R := Function.update (Function.update S.R 139 []) 143 folded}
  have select : Runs body (gatherRecords 110 139 94 106 0 1 2 143 0 pairRe) S S₁ (s*(16*w+10)+16) := by
    intro vi
    obtain ⟨vf,m,hu,hm,he⟩ := boundaryRhsHaloGather_exec (body := body) (src := 110) (mask := 139) (width := 94)
      (symbols := 106) (ts := 0) (tm := 1) (acc := 2) (out := 143) (cs := 0) (by decide) hst hA band a b hb C w tail vi S
      hsrc hmask hw (by
        intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact h106
        all_goals exact hblank _ (by decide))
    exact ⟨vf,m,hu,hm,by simpa [S₁,ordered,B,h143] using he⟩
  have fold : Runs body preparedBoundaryRhsFold S₁ S₂ (250*(B.card+1)*(w+1)) := by
    intro vi
    obtain ⟨vf,m,hu,hm,he⟩ := preparedBoundaryRhsFold_exec (body := body) s B C w vi S₁
      (by simp [S₁,ordered]) (by simpa [S₁] using hw) (by simpa [S₁,B] using hcount)
      (by intro r hr; have hn : r ≠ 143 := by intro hh; subst r; norm_num at hr
          simpa [S₁,hn] using hblank r hr) hleft
    exact ⟨vf,m,hu,hm,by simpa [S₁,S₂,folded] using he⟩
  have erase : Runs body (uclear 139) S₂ S₃ (2*s+2) := by
    apply Runs.of_exact
    intro vi
    obtain ⟨vf,hu,he⟩ := uclear_exec (body := body) 139 vi S₂
    refine ⟨vf,hu,he.cast ?_ ?_⟩
    · simp [S₂,hmask,couplingSourceMaskSymbols]
    · apply congrArg (mk vf)
      simp [S₃,S₂,Function.update_comm (by decide : (139 : Fin 148) ≠ 143)]
  have hN : B.card ≤ s := by simpa [B] using Finset.card_le_univ (s := B)
  have hscale := Nat.mul_le_mul_right (w+1) (Nat.succ_le_succ hN)
  exact ((select.seq (fold.seq erase)).mono (by nlinarith only [hscale])) v

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
