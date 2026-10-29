module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparePackedBoundaryFold
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryRhsFold

/-! Count and isolate an ordered packed boundary RHS, execute the existing fold,
publish the folded line and release every temporary control. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def closedPackedBoundaryRhsFold : Pr P 168 Q A U :=
  .seq preparePackedBoundaryFold (.seq packedBoundaryRhsFold
    (.seq (moveR 6 1 id) (.seq (moveR 1 143 id) (clearWords [0,2,3]))))

def closedPackedBoundaryRhsFoldCost (N n w : ℕ) : ℕ :=
  preparePackedBoundaryFoldCost N n w+70*(n+1)*(w+1)+71

theorem closedPackedBoundaryRhsFold_exec {s t origin N : ℕ} [NeZero s]
    (hst : s < t) (hA : 4 ≤ A) (band a b : ℕ) (hb : b ≤ s) (hfit : origin+N ≤ s)
    (hB : ∀ i ∈ haloBoundary s t band a b, origin ≤ i.val ∧ i.val < origin+N)
    (C : ZMod s → GaussianInt) (w : ℕ) (tail : List (Fin (A+4)))
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hmask : S.R 167 = couplingSourceIntervalMaskSymbols true A s t band a b origin N)
    (hsrc : S.R 93 = cstream A w ((bOrder s (haloBoundary s t band a b)).map C)++tail)
    (hw : (S.R 130).length = w) (hblank : ∀ k : Fin 168, k.val < 77 → S.R k = [])
    (h116 : S.R 116 = []) (h143 : S.R 143 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ closedPackedBoundaryRhsFoldCost N (haloBoundary s t band a b).card w ∧
      Exec body closedPackedBoundaryRhsFold (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          116 (List.replicate (haloBoundary s t band a b).card tick)) 93 tail)
          143 (cstream A w ((bFoldOrder s (haloBoundary s t band a b)).map C)))}) := by
  let B := haloBoundary s t band a b
  let n := B.card
  let words := cstream A w ((bOrder s B).map C)
  let output := cstream A w ((bFoldOrder s B).map C)
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := preparePackedBoundaryFold_exec (body := body) hst hA band a b hb hfit hB
    C w tail v S hmask hsrc hw (by intro k hk; exact hblank k (by omega)) h116 h143
  let S₁ : Stacks 168 A := {S with R := packedBoundaryFoldInputR n w words tail S.R}
  have hlow : ∀ r : Fin 168, 6 ≤ r.val → r.val < 77 → S₁.R r = [] := by
    intro r hr hr'
    have hn (j : Fin 168) (hj : j.val < 6 ∨ 77 ≤ j.val) : r ≠ j := by
      intro he; have hv := congrArg Fin.val he; rcases hj with hj | hj <;> omega
    simpa [S₁,packedBoundaryFoldInputR,hn 0 (by decide),hn 2 (by decide),hn 3 (by decide),
      hn 93 (by decide),hn 116 (by decide),hn 143 (by decide)] using hblank r hr'
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := packedBoundaryRhsFold_exec (body := body) s B C w v₁ S₁
    (by simp [S₁,packedBoundaryFoldInputR,words]) (by simpa [S₁,packedBoundaryFoldInputR] using hw)
    (by simp [S₁,packedBoundaryFoldInputR,n]) (by simp [S₁,packedBoundaryFoldInputR,n])
    (by simp [S₁,packedBoundaryFoldInputR,n]) (by simp [S₁,packedBoundaryFoldInputR,n]) hlow
  let S₂ : Stacks 168 A := {S₁ with R := (Function.update (Function.update S₁.R 143 []) 6 output)}
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec body 6 1 (by decide) id v₂ S₂
  let S₃ : Stacks 168 A := {S₂ with R := movedR S₂.R 6 1 id (S₂.R 6)}
  have houtlen : output.length = n*w := by simp [output,n,bFoldOrder]
  have h1len : (S₃.R 1).length = n*w := by
    simp [S₃,movedR,S₂,S₁,packedBoundaryFoldInputR,hblank 1 (by decide),houtlen]
  obtain ⟨v₄,hu₄,he₄⟩ := moveR_exec body 1 143 (by decide) id v₃ S₃
  let S₄ : Stacks 168 A := {S₃ with R := movedR S₃.R 1 143 id (S₃.R 1)}
  obtain ⟨v₅,hu₅,he₅⟩ := clearWords_exec (body := body) [(0 : Fin 168),2,3] (by decide) v₄ S₄
  have hsum : ([(0 : Fin 168),2,3].map (fun r => (S₄.R r).length)).sum =
      n/2+((n+1)/2-n/2)+((n+1)/2)*w := by
    simp [S₄,S₃,S₂,S₁,packedBoundaryFoldInputR,movedR,Nat.add_assoc]
  refine ⟨v₅,m₁+(m₂+((2*(n*w)+2)+((2*(n*w)+2)+(2*(n/2+((n+1)/2-n/2)+((n+1)/2)*w)+7)))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),?_,
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))).cast ?_ ?_⟩
  · change _ ≤ preparePackedBoundaryFoldCost N n w+70*(n+1)*(w+1)+71
    change m₂ ≤ 60*(n+1)*w+60*n+60 at hm₂
    have hhalf : (n+1)/2 ≤ n := by omega
    have hpar : n/2+((n+1)/2-n/2) = (n+1)/2 := by omega
    have hprod := Nat.mul_le_mul_right w hhalf
    rw [hpar]
    nlinarith only [hm₁,hm₂,hhalf,hprod]
  · simp only [S₂,Function.update_self,houtlen,h1len,hsum,List.length_cons,List.length_nil]
  · apply congrArg (mk v₅)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h0 : k = 0 <;> by_cases h1 : k = 1 <;> by_cases h2 : k = 2 <;>
      by_cases h3 : k = 3 <;> by_cases h6 : k = 6 <;> by_cases h143' : k = 143 <;>
      simp [S₄,S₃,S₂,S₁,packedBoundaryFoldInputR,movedR,h0,h1,h2,h3,h6,h143',output,n,B,
        hblank 0 (by decide),hblank 1 (by decide),hblank 2 (by decide),
        hblank 3 (by decide),hblank 6 (by decide),Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
