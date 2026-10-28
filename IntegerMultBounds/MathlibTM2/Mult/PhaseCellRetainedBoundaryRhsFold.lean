module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRhsFoldPlacement

/-! Execute the canonical RHS fold while preserving the retained coordinate bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 148 Q A U}

def retainedBoundaryRhsFold : Pr P₀ 148 Q A U := bandFoldLineP BoundaryRhsFoldPlacement.reg

theorem retainedBoundaryRhsFold_exec (s : ℕ) [NeZero s] (B : Finset (ZMod s))
    (C : ZMod s → GaussianInt) (w : ℕ) (v : HS 148 Q A U) (S : Stacks 148 A)
    (hsource : S.R 143 = cstream A w ((bOrder s B).map C))
    (hwidth : (S.R 94).length = w) (hcount : (S.R 116).length = B.card)
    (hfloor : (S.R 0).length = B.card/2)
    (hparity : (S.R 2).length = (B.card+1)/2-B.card/2)
    (hbytes : (S.R 3).length = (B.card+1)/2*w)
    (hblank : ∀ r : Fin 148, 6 ≤ r.val → r.val < 77 → S.R r = [])
    (hleft : ∀ r, S.L r = []) :
    let output := cstream A w ((bFoldOrder s B).map C)
    ∃ v' m, v'.user = v.user ∧
      m ≤ 60*(B.card+1)*w+60*B.card+60 ∧
      Exec body retainedBoundaryRhsFold (mk v S) m
        (mk v' {S with R := Function.update (Function.update S.R 143 []) 6 output}) := by
  dsimp only
  let σ := fun r => S.R (BoundaryRhsFoldPlacement.reg r)
  have hc : RsbClean BoundaryFoldPlacement.mul S := by
    refine ⟨hleft,?_⟩
    intro i
    apply hblank _ <;> simp [BoundaryFoldPlacement.mul] <;> omega
  have hs : RsbHolds BoundaryRhsFoldPlacement.reg S σ := fun _ => rfl
  have hh := boundaryRhsFold_runs (body := body) BoundaryRhsFoldPlacement.reg_injective
    BoundaryRhsFoldPlacement.reg_mul s B C w σ
    (by simpa [σ] using hsource) (by simpa [σ] using hbytes)
    (by simpa [σ] using hfloor) (by simpa [σ] using hparity)
    (by simpa [σ] using hcount) (by simpa [σ] using hwidth)
    (by simpa [σ] using hblank 6 (by decide) (by decide))
    (by simpa [σ] using hblank 7 (by decide) (by decide))
    (by simpa [σ] using hblank 8 (by decide) (by decide))
    (by simpa [σ] using hblank 9 (by decide) (by decide))
    (by simpa [σ] using hblank 10 (by decide) (by decide))
    (by simpa [σ] using hblank 11 (by decide) (by decide))
    (by simpa [σ] using hblank 12 (by decide) (by decide))
  obtain ⟨v',S',m,hu,hm,he,hs',hf⟩ := hh v S hc hs
  refine ⟨v',m,hu,hm,he.cast rfl ?_⟩
  apply congrArg (mk v')
  refine Stacks.ext hf.1 hf.2.1 hf.2.2.1 ?_
  funext k
  by_cases h143 : k = 143
  · subst k
    simpa [σ] using hs' .sel
  by_cases h6 : k = 6
  · subst k
    simpa [σ] using hs' .vk
  simp only [Function.update_of_ne h6,Function.update_of_ne h143]
  by_cases hr : ∃ r, BoundaryRhsFoldPlacement.reg r = k
  · obtain ⟨r,rfl⟩ := hr
    have hsel : r ≠ .sel := by intro he; subst r; exact h143 (by simp)
    have hvk : r ≠ .vk := by intro he; subst r; exact h6 (by simp)
    simpa [σ,hsel,hvk] using hs' r
  · exact hf.2.2.2 k (fun r he => hr ⟨r,he⟩)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
