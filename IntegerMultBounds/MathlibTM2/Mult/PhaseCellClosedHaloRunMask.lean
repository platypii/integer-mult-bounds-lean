module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloRunMaskFromHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationWidth

/-! Generate and release the geometry width around the complete interval mask pipeline. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

def closedHaloRunMask (off on : Fin (A+4)) : Pr P 117 Q A U :=
  .seq generatePublicationWidth (.seq (haloRunMaskFromHeaders off on) (uclear 115))

def closedHaloRunMaskCost (s t band a b : ℕ) : ℕ :=
  let W := publicationGeometryWidth t band
  generatePublicationWidthCost t band+haloRunMaskFromHeadersCost W s t band a b+2*W+2

theorem closedHaloRunMask_exec {s t band a b : ℕ} [NeZero s]
    (hst : s < t) (has : a ≤ s) (hbs : b ≤ s) (hA : 4 ≤ A) (off on : Fin (A+4))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hs : (S.R 97).length = s) (ht : (S.R 98).length = t)
    (hband : (S.R 100).length = band) (ha : (S.R 101).length = a) (hb : (S.R 103).length = b)
    (h115 : S.R 115 = []) (h106 : S.R 106 = []) (h108 : S.R 108 = [])
    (hblank : ∀ r : Fin 117, r.val < 31 → S.R r = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ closedHaloRunMaskCost s t band a b ∧
      Exec body (closedHaloRunMask off on) (mk v S) n
        (mk v' {S with R := (Function.update S.R 109
          ((List.range s).map (fun k => if haloInteriorAt s t band a b k then on else off)++S.R 109))}) := by
  let W := publicationGeometryWidth t band
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := generatePublicationWidth_exec (body := body) t band v S ht hband h115 (by
    intro k hk
    have hk31 : k.val < 31 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
    exact hblank k hk31)
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 115 (List.replicate W tick)}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := haloRunMaskFromHeaders_exec (body := body)
    hst has hbs (publicationGeometryWidth_fits t band) hA off on v₁ S₁
    (by simpa [S₁] using hs) (by simpa [S₁] using ht) (by simpa [S₁] using hband)
    (by simpa [S₁] using ha) (by simpa [S₁] using hb) (by simp [S₁,W])
    (by simpa [S₁] using h106) (by simpa [S₁] using h108) (by
      intro r hr
      have hr115 : r ≠ (115 : Fin 117) := by intro he; subst r; norm_num at hr
      simpa [S₁,hr115] using hblank r hr)
  let mask := (List.range s).map (fun k => if haloInteriorAt s t band a b k then on else off)
  let S₂ : Stacks 117 A := {S₁ with R := Function.update S₁.R 109 (mask++S₁.R 109)}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) 115 v₂ S₂
  refine ⟨v₃,n₁+(n₂+(2*W+2)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · dsimp only [closedHaloRunMaskCost]; omega
  · simp [S₂,S₁]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp only [S₂,S₁,Function.update_apply]
    split_ifs <;> simp_all [mask]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
