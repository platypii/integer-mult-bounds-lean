module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedHaloRunMask
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryWindowMask

/-! Generate the complete recovery mask from ordinary scalar headers with one geometry width. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

def closedRecoveryRunMask (boundary : Bool) : Pr P 117 Q A U :=
  .seq generatePublicationWidth
    (.seq (haloRunMaskFromHeaders (pairSym A false false) (pairSym A boundary boundary))
      (.seq recoveryWindowMask (uclear 115)))

def closedRecoveryRunMaskCost (s t B a b : ℕ) : ℕ :=
  closedHaloRunMaskCost s t B a b+recoveryWindowMaskCost (publicationGeometryWidth t B) s t B a b

theorem closedRecoveryRunMask_exec (boundary : Bool) {s t B a b : ℕ} [NeZero s]
    (hst : s < t) (has : a ≤ s) (hbs : b ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hs : (S.R 97).length = s) (ht : (S.R 98).length = t)
    (hB : (S.R 100).length = B) (ha : (S.R 101).length = a) (hb : (S.R 103).length = b)
    (h115 : S.R 115 = []) (h106 : S.R 106 = []) (h108 : S.R 108 = [])
    (hblank : ∀ r : Fin 117, r.val < 31 → S.R r = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ closedRecoveryRunMaskCost s t B a b ∧
      Exec body (closedRecoveryRunMask boundary) (mk v S) n
        (mk v' {S with R := Function.update S.R 109 (recoveryGuardMaskSymbols boundary A s t B a b++S.R 109)}) := by
  let W := publicationGeometryWidth t B
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := generatePublicationWidth_exec (body := body) t B v S ht hB h115 (by
    intro k hk
    have hk31 : k.val < 31 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
    exact hblank k hk31)
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 115 (List.replicate W tick)}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := haloRunMaskFromHeaders_exec (body := body)
    hst has hbs (publicationGeometryWidth_fits t B) hA (pairSym A false false) (pairSym A boundary boundary)
    v₁ S₁ (by simpa [S₁] using hs) (by simpa [S₁] using ht) (by simpa [S₁] using hB)
    (by simpa [S₁] using ha) (by simpa [S₁] using hb) (by simp [S₁,W])
    (by simpa [S₁] using h106) (by simpa [S₁] using h108) (by
      intro r hr
      have hr115 : r ≠ (115 : Fin 117) := by intro he; subst r; norm_num at hr
      simpa [S₁,hr115] using hblank r hr)
  let S₂ : Stacks 117 A := {S₁ with R := (Function.update S₁.R 109
    (recoveryInteriorSymbols boundary A s t B a b++S₁.R 109))}
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := recoveryWindowMask_exec (body := body) boundary
    hst has hbs (publicationGeometryWidth_fits t B) v₂ S₂ (S.R 109)
    (by simpa [S₂,S₁] using hs) (by simpa [S₂,S₁] using ht) (by simpa [S₂,S₁] using hB)
    (by simpa [S₂,S₁] using ha) (by simpa [S₂,S₁] using hb) (by simp [S₂,S₁,W])
    (by simpa [S₂,S₁] using h106) (by simpa [S₂,S₁] using h108) (by
      intro r hr
      have hr115 : r ≠ (115 : Fin 117) := by intro he; subst r; norm_num at hr
      have hr109 : r ≠ (109 : Fin 117) := by intro he; subst r; norm_num at hr
      simpa [S₂,S₁,hr115,hr109] using hblank r hr) (by simp [S₂,S₁])
  let S₃ : Stacks 117 A := {S₂ with R := (Function.update S₂.R 109
    (recoveryGuardMaskSymbols boundary A s t B a b++S.R 109))}
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := body) 115 v₃ S₃
  refine ⟨v₄,n₁+(n₂+(n₃+(2*W+2))),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))).cast ?_ ?_⟩
  · dsimp only [closedRecoveryRunMaskCost,closedHaloRunMaskCost]; omega
  · simp [S₃,S₂,S₁]
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp only [S₃,S₂,S₁,Function.update_apply]
    split_ifs <;> simp_all

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
