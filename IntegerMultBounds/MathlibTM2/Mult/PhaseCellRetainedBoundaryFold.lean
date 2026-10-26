module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFoldPlacement

/-! Execute the canonical coordinate fold in the retained register bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 148 Q A U}

def retainedBoundaryFold : Pr P₀ 148 Q A U := bandFoldLineP BoundaryFoldPlacement.reg

theorem retainedBoundaryFold_exec {s t : ℕ} [NeZero s] (hst : s < t)
    (band a b w : ℕ) (hb : b ≤ s) (v : HS 148 Q A U) (S : Stacks 148 A)
    (hsource : S.R 109 = boundaryOrderSymbols A w s t band a b)
    (hwidth : (S.R 115).length = w) (hcount : (S.R 116).length = (haloBoundary s t band a b).card)
    (hfloor : (S.R 0).length = (haloBoundary s t band a b).card/2)
    (hparity : (S.R 2).length = ((haloBoundary s t band a b).card+1)/2-(haloBoundary s t band a b).card/2)
    (hbytes : (S.R 3).length = ((haloBoundary s t band a b).card+1)/2*w)
    (hblank : ∀ r : Fin 148, 6 ≤ r.val → r.val < 77 → S.R r = [])
    (hleft : ∀ r, S.L r = []) :
    let output := cstream A w ((bFoldOrder s (haloBoundary s t band a b)).map
      (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)))
    ∃ v' m, v'.user = v.user ∧
      m ≤ 60*((haloBoundary s t band a b).card+1)*w+60*(haloBoundary s t band a b).card+60 ∧
      Exec body retainedBoundaryFold (mk v S) m
        (mk v' {S with R := Function.update (Function.update S.R 109 []) 6 output}) := by
  dsimp only
  let σ := fun r => S.R (BoundaryFoldPlacement.reg r)
  have hc : RsbClean BoundaryFoldPlacement.mul S := by
    refine ⟨hleft,?_⟩
    intro i
    apply hblank _ <;> simp [BoundaryFoldPlacement.mul] <;> omega
  have hs : RsbHolds BoundaryFoldPlacement.reg S σ := fun _ => rfl
  have hh := boundaryFold_runs (body := body) BoundaryFoldPlacement.reg_injective
    BoundaryFoldPlacement.reg_mul hst band a b w hb σ
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
  by_cases h109 : k = 109
  · subst k
    simpa [σ] using hs' .sel
  by_cases h6 : k = 6
  · subst k
    simpa [σ] using hs' .vk
  simp only [Function.update_of_ne h6,Function.update_of_ne h109]
  by_cases hr : ∃ r, BoundaryFoldPlacement.reg r = k
  · obtain ⟨r,rfl⟩ := hr
    have hsel : r ≠ .sel := by intro he; subst r; exact h109 (by simp)
    have hvk : r ≠ .vk := by intro he; subst r; exact h6 (by simp)
    simpa [σ,hsel,hvk] using hs' r
  · exact hf.2.2.2 k (fun r he => hr ⟨r,he⟩)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
