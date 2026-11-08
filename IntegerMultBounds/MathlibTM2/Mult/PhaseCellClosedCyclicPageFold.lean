module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCyclicBoundaryFold
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFoldCounters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedBoundaryFold

/-! Generate fold controls from the emitted cyclic page, fold it, and retire the controls. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 148 Q A U}

def closedCyclicPageFold : Pr P 148 Q A U :=
  .seq (embProg boundaryInputReg Empty.elim (boundaryFoldCounters (P₀ := Empty)))
    (.seq retainedBoundaryFold (.seq (moveR 6 1 id) (.seq (moveR 1 109 id) (clearWords [0,2,3]))))

def closedCyclicPageFoldCost (N w : ℕ) : ℕ :=
  boundaryFoldCountersCost N w+70*(N+1)*(w+1)+71

theorem closedCyclicPageFold_exec {s t : ℕ} [NeZero s] (hst : s < t)
    (band a n w : ℕ) (ha : a < s) (hn : n ≤ s) (v : HS 148 Q A U) (S : Stacks 148 A)
    (hsource : S.R 109 = cstream A w (cyclicBoundaryIndexWords s t band a n))
    (hwidth : (S.R 115).length = w) (hcount : (S.R 116).length = (cyclicPrincipalBoundary s t band a n).card)
    (hblank : ∀ k : Fin 148, k.val < 77 → S.R k = []) (hleft : ∀ k, S.L k = []) :
    let N := (cyclicPrincipalBoundary s t band a n).card
    let output := cstream A w ((bFoldOrder s (cyclicPrincipalBoundary s t band a n)).map
      (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)))
    ∃ v' m, v'.user = v.user ∧ m ≤ closedCyclicPageFoldCost N w ∧
      Exec body closedCyclicPageFold (mk v S) m
        (mk v' {S with R := Function.update S.R 109 output}) := by
  dsimp only
  let N := (cyclicPrincipalBoundary s t band a n).card
  let output := cstream A w ((bFoldOrder s (cyclicPrincipalBoundary s t band a n)).map
    (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)))
  let E := embStk boundaryInputReg S
  obtain ⟨vi,m₁,hvi,hm₁,hei⟩ := boundaryFoldCounters_exec (body := fun e : Empty => nomatch e)
    N w (embDn boundaryInputReg v) E hcount hwidth (by intro k hk; exact hblank _ (by simp [boundaryInputReg]; omega))
  obtain ⟨v₁,_,hv₁,he₁⟩ := exec_emb_ovr (e := boundaryInputReg) (ι := Empty.elim) (body' := body)
    boundaryInputReg_injective (fun e => nomatch e) hei v rfl S rfl
  let S₁ : Stacks 148 A := {S with R := (Function.update (Function.update (Function.update S.R
    0 (List.replicate (N/2) tick)) 2 (List.replicate ((N+1)/2-N/2) tick)) 3 (List.replicate (((N+1)/2)*w) tick))}
  have he₁' : Exec body (embProg boundaryInputReg Empty.elim (boundaryFoldCounters (P₀ := Empty)))
      (mk v S) m₁ (mk v₁ S₁) := by
    convert he₁ using 1
    apply congrArg (mk v₁)
    let E₁ : Stacks 117 A := {E with R := Function.update E.R 0 (List.replicate (N/2) tick)}
    let E₂ : Stacks 117 A := {E₁ with R := Function.update E₁.R 2 (List.replicate ((N+1)/2-N/2) tick)}
    symm
    change embOvr boundaryInputReg ({E₂ with R := Function.update E₂.R 3 (List.replicate (((N+1)/2)*w) tick)}).get S = _
    rw [embOvr_updR boundaryInputReg_injective E₂ S 3 _]
    dsimp only [E₂]
    rw [embOvr_updR boundaryInputReg_injective E₁ S 2 _]
    dsimp only [E₁,E]
    rw [embOvr_updR boundaryInputReg_injective (embStk boundaryInputReg S) S 0 _,embOvr_stk]
    rfl
  have hlow : ∀ k : Fin 148, 6 ≤ k.val → k.val < 77 → S₁.R k = [] := by
    intro k hk hk'
    have h0 : k ≠ 0 := by intro h; subst k; norm_num at hk
    have h2 : k ≠ 2 := by intro h; subst k; norm_num at hk
    have h3 : k ≠ 3 := by intro h; subst k; norm_num at hk
    simpa [S₁,h0,h2,h3] using hblank k hk'
  obtain ⟨v₂,m₂,hv₂,hm₂,he₂⟩ := retainedCyclicBoundaryFold_exec (body := body)
    hst band a n w ha hn v₁ S₁ (by simpa [S₁] using hsource)
    (by simpa [S₁] using hwidth) (by simpa [S₁] using hcount)
    (by simp [S₁,N]) (by simp [S₁,N]) (by simp [S₁,N]) hlow hleft
  let S₂ : Stacks 148 A := {S₁ with R := Function.update (Function.update S₁.R 109 []) 6 output}
  obtain ⟨v₃,hv₃,he₃⟩ := moveR_exec body 6 1 (by decide) id v₂ S₂
  let S₃ : Stacks 148 A := {S₂ with R := movedR S₂.R 6 1 id (S₂.R 6)}
  have houtlen : output.length = N*w := by simp [output,N,bFoldOrder]
  have h1len : (S₃.R 1).length = N*w := by simp [S₃,movedR,S₂,S₁,hblank 1 (by decide),houtlen]
  obtain ⟨v₄,hv₄,he₄⟩ := moveR_exec body 1 109 (by decide) id v₃ S₃
  let S₄ : Stacks 148 A := {S₃ with R := movedR S₃.R 1 109 id (S₃.R 1)}
  obtain ⟨v₅,hv₅,he₅⟩ := clearWords_exec (body := body) [(0 : Fin 148),2,3] (by decide) v₄ S₄
  have hsum : ([(0 : Fin 148),2,3].map (fun k => (S₄.R k).length)).sum =
      N/2+((N+1)/2-N/2)+((N+1)/2)*w := by simp [S₄,S₃,S₂,S₁,movedR,Nat.add_assoc]
  refine ⟨v₅,m₁+(m₂+((2*(N*w)+2)+((2*(N*w)+2)+(2*(N/2+((N+1)/2-N/2)+((N+1)/2)*w)+7)))),
    hv₅.trans (hv₄.trans (hv₃.trans (hv₂.trans (hv₁.trans hvi)))),?_,
    (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))).cast ?_ ?_⟩
  · change _ ≤ boundaryFoldCountersCost N w+70*(N+1)*(w+1)+71
    have hhalf : (N+1)/2 ≤ N := by omega
    have hpar : N/2+((N+1)/2-N/2) = (N+1)/2 := by omega
    have hprod := Nat.mul_le_mul_right w hhalf
    change m₂ ≤ 60*(N+1)*w+60*N+60 at hm₂
    rw [hpar]
    nlinarith only [hm₁,hm₂,hhalf,hprod]
  · simp only [S₂,Function.update_self,houtlen,h1len,hsum,List.length_cons,List.length_nil]
  · apply congrArg (mk v₅)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h0 : k = 0 <;> by_cases h1 : k = 1 <;> by_cases h2 : k = 2 <;>
      by_cases h3 : k = 3 <;> by_cases h6 : k = 6 <;> by_cases h109 : k = 109 <;>
      simp [S₄,S₃,S₂,S₁,movedR,h0,h1,h2,h3,h6,h109,output,
        hblank 0 (by decide),hblank 1 (by decide),hblank 2 (by decide),
        hblank 3 (by decide),hblank 6 (by decide)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
