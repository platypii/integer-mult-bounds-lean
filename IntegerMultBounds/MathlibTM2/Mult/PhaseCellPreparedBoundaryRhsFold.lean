module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedBoundaryRhsFold
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRhsFoldCounters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrefixRelease
public import IntegerMultBounds.MathlibTM2.Host.RunContract

/-! Generate counters, fold the selected RHS and release every temporary counter. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 148 Q A U}

def preparedBoundaryRhsFold : Pr P 148 Q A U :=
  .seq boundaryRhsFoldCounters (.seq retainedBoundaryRhsFold
    (.seq (moveR 6 1 id) (.seq (moveR 1 143 id) (clearWords [0,2,3]))))

theorem preparedBoundaryRhsFold_exec (s : ℕ) [NeZero s] (B : Finset (ZMod s))
    (C : ZMod s → GaussianInt) (w : ℕ) (v : HS 148 Q A U) (S : Stacks 148 A)
    (hsource : S.R 143 = cstream A w ((bOrder s B).map C))
    (hwidth : (S.R 94).length = w) (hcount : (S.R 116).length = B.card)
    (hblank : ∀ r : Fin 148, r.val < 77 → S.R r = []) (hleft : ∀ r, S.L r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 250*(B.card+1)*(w+1) ∧
      Exec body preparedBoundaryRhsFold (mk v S) m
        (mk v' {S with R := Function.update S.R 143 (cstream A w ((bFoldOrder s B).map C))}) := by
  let n := B.card
  let output := cstream A w ((bFoldOrder s B).map C)
  let S₁ : Stacks 148 A := {S with R := (Function.update (Function.update (Function.update S.R
    0 (List.replicate (n/2) tick)) 2 (List.replicate ((n+1)/2-n/2) tick))
    3 (List.replicate (((n+1)/2)*w) tick))}
  let S₂ : Stacks 148 A := {S₁ with R := Function.update (Function.update S₁.R 143 []) 6 output}
  let S₃ : Stacks 148 A := {S₂ with R := Function.update (Function.update S₂.R 6 []) 1 output.reverse}
  let S₄ : Stacks 148 A := {S₃ with R := Function.update (Function.update S₃.R 1 []) 143 output}
  let S₅ : Stacks 148 A := {S with R := Function.update S.R 143 output}
  have hlen : output.length = n*w := by simp [output,n,bFoldOrder]
  have setup : Runs body boundaryRhsFoldCounters S S₁ (boundaryFoldCountersCost n w) := by
    intro vi
    exact boundaryRhsFoldCounters_exec n w vi S hcount hwidth (fun r hr => hblank r (by omega))
  have fold : Runs body retainedBoundaryRhsFold S₁ S₂ (60*(n+1)*w+60*n+60) := by
    intro vi
    apply retainedBoundaryRhsFold_exec s B C w vi S₁
    · simpa [S₁] using hsource
    · simpa [S₁] using hwidth
    · simpa [S₁] using hcount
    · simp [S₁,n]
    · simp [S₁,n]
    · simp [S₁,n]
    · intro r hr6 hr77
      have h0 : r ≠ 0 := by intro hh; subst r; norm_num at hr6
      have h2 : r ≠ 2 := by intro hh; subst r; norm_num at hr6
      have h3 : r ≠ 3 := by intro hh; subst r; norm_num at hr6
      simpa [S₁,h0,h2,h3] using hblank r hr77
    · exact hleft
  have move₁ : Runs body (moveR 6 1 id) S₂ S₃ (2*(n*w)+2) := by
    apply Runs.of_exact
    intro vi
    obtain ⟨vf,hu,he⟩ := moveR_exec (body := body) 6 1 (by decide) id vi S₂
    refine ⟨vf,hu,he.cast ?_ ?_⟩
    · simp [S₂,hlen]
    · apply congrArg (mk vf)
      simp [S₃,S₂,S₁,movedR,hblank 1 (by decide)]
  have move₂ : Runs body (moveR 1 143 id) S₃ S₄ (2*(n*w)+2) := by
    apply Runs.of_exact
    intro vi
    obtain ⟨vf,hu,he⟩ := moveR_exec (body := body) 1 143 (by decide) id vi S₃
    refine ⟨vf,hu,he.cast ?_ ?_⟩
    · simp [S₃,hlen]
    · apply congrArg (mk vf)
      simp [S₄,S₃,S₂,movedR]
  have release : Runs body (clearWords [0,2,3]) S₄ S₅
      (2*(n/2+((n+1)/2-n/2)+(n+1)/2*w)+7) := by
    apply Runs.of_exact
    intro vi
    obtain ⟨vf,hu,he⟩ := clearWords_exec (body := body) [0,2,3] (by decide) vi S₄
    refine ⟨vf,hu,he.cast ?_ ?_⟩
    · simp [S₄,S₃,S₂,S₁,Nat.add_assoc]
    · apply congrArg (mk vf)
      refine Stacks.ext rfl rfl rfl ?_
      funext r
      by_cases h0 : r = 0
      · subst r; simp [S₅,hblank 0 (by decide)]
      by_cases h2 : r = 2
      · subst r; simp [S₅,hblank 2 (by decide)]
      by_cases h3 : r = 3
      · subst r; simp [S₅,hblank 3 (by decide)]
      by_cases h6 : r = 6
      · subst r; simp [S₅,S₄,S₃,hblank 6 (by decide)]
      by_cases h1 : r = 1
      · subst r; simp [S₅,S₄,hblank 1 (by decide)]
      by_cases h143 : r = 143
      · subst r; simp [S₅,S₄]
      simp [S₅,S₄,S₃,S₂,S₁,h0,h2,h3,h6,h1,h143]
  have hhalf : (n+1)/2 ≤ n+1 := Nat.div_le_self _ _
  have hfloor : n/2 ≤ n := Nat.div_le_self _ _
  have hparity : (n+1)/2-n/2 ≤ n+1 := (Nat.sub_le _ _).trans hhalf
  have hbytes := Nat.mul_le_mul_right w hhalf
  exact ((setup.seq (fold.seq (move₁.seq (move₂.seq release)))).mono (by
    dsimp only [boundaryFoldCountersCost]
    nlinarith only [hfloor,hparity,hbytes])) v

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
