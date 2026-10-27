module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySetupHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTableBoundaryFold

/-! Generate the retained folded page from the ordinary master headers and release setup controls. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

def prepareBoundaryPage : Pr P 154 Q A U :=
  .seq installBoundarySetupHeaders (.seq tableBoundaryFold releaseBoundarySetupHeaders)

def prepareBoundaryPageCost (s t band a b : ℕ) [NeZero s] : ℕ :=
  (4*(s+t+band+a+b)+21)+(closedBoundaryFoldCost s t band a b+(2*(s+t+band+a+b)+11))

theorem prepareBoundaryPage_exec {s t band a b : ℕ} [NeZero s]
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (v : HS 154 Q A U) (S : Stacks 154 A)
    (hs : (S.R 121).length = s) (ht : (S.R 122).length = t) (hband : (S.R 124).length = band)
    (ha : (S.R 141).length = a) (hb : (S.R 142).length = b) (h135 : S.R 135 = [])
    (h115 : S.R 115 = []) (h116 : S.R 116 = []) (h109 : S.R 109 = [])
    (h106 : S.R 106 = []) (h108 : S.R 108 = [])
    (hblank : ∀ k ∈ boundarySetupHeaders, S.R k = [])
    (hlow : ∀ r : Fin 154, r.val < 77 → S.R r = [])
    (hleft : ∀ r : Fin 148, S.L (tableFoldReg r) = []) :
    let V := publicationGeometryWidth t band
    let n := (haloBoundary s t band a b).card
    let page := cstream A V ((bFoldOrder s (haloBoundary s t band a b)).map
      (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)))
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareBoundaryPageCost s t band a b ∧
      Exec body prepareBoundaryPage (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          115 (List.replicate V tick)) 116 (List.replicate n tick)) 109 page)}) := by
  dsimp only
  let V := publicationGeometryWidth t band
  let n := (haloBoundary s t band a b).card
  let page := cstream A V ((bFoldOrder s (haloBoundary s t band a b)).map
    (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)))
  obtain ⟨v₁,hu₁,he₁⟩ := installBoundarySetupHeaders_exec (body := body) s t band a b v S hs ht hband ha hb h135
  let S₁ : Stacks 154 A := {S with R := boundarySetupR s t band a b S.R}
  have hoff (k : Fin 154) (hk : k ∉ boundarySetupHeaders) : S₁.R k = S.R k := boundarySetupR_off s t band a b S.R k hk
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := tableBoundaryFold_exec (body := body) hst haS hbS hbandS v₁ S₁
    (by simp [S₁,boundarySetupR,unaryCopiesR,boundarySetupCopies,boundarySetupValue,hblank 97 (by decide)])
    (by simp [S₁,boundarySetupR,unaryCopiesR,boundarySetupCopies,boundarySetupValue,hblank 98 (by decide)])
    (by simp [S₁,boundarySetupR,unaryCopiesR,boundarySetupCopies,boundarySetupValue,hblank 100 (by decide)])
    (by simp [S₁,boundarySetupR,unaryCopiesR,boundarySetupCopies,boundarySetupValue,hblank 101 (by decide)])
    (by simp [S₁,boundarySetupR,unaryCopiesR,boundarySetupCopies,boundarySetupValue,hblank 103 (by decide)])
    (by rw [hoff 115 (by decide)]; exact h115) (by rw [hoff 116 (by decide)]; exact h116)
    (by rw [hoff 109 (by decide)]; exact h109) (by rw [hoff 106 (by decide)]; exact h106)
    (by rw [hoff 108 (by decide)]; exact h108) (by
      intro r hr
      have hk : r ∉ boundarySetupHeaders := by
        intro hk
        simp only [boundarySetupHeaders,List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> norm_num at hr
      rw [hoff r hk]
      exact hlow r hr) hleft
  let S₂ : Stacks 154 A := {S₁ with R := (Function.update (Function.update (Function.update S₁.R
    115 (List.replicate V tick)) 116 (List.replicate n tick)) 109 page)}
  let Sfinal : Stacks 154 A := {S with R := (Function.update (Function.update (Function.update S.R
    115 (List.replicate V tick)) 116 (List.replicate n tick)) 109 page)}
  have hover : {Sfinal with R := boundarySetupR s t band a b Sfinal.R} = S₂ := by
    simp only [Sfinal,S₂,S₁]
    rw [boundarySetupR_update s t band a b _ 109 page (by decide),
      boundarySetupR_update s t band a b _ 116 _ (by decide),
      boundarySetupR_update s t band a b _ 115 _ (by decide)]
  obtain ⟨v₃,hu₃,he₃⟩ := releaseBoundarySetupHeaders_exec (body := body) s t band a b v₂ Sfinal (by
    intro k hk
    have h115 : k ≠ 115 := by intro h; subst k; norm_num [boundarySetupHeaders] at hk
    have h116 : k ≠ 116 := by intro h; subst k; norm_num [boundarySetupHeaders] at hk
    have h109 : k ≠ 109 := by intro h; subst k; norm_num [boundarySetupHeaders] at hk
    simpa [Sfinal,h115,h116,h109] using hblank k hk)
  rw [hover] at he₃
  refine ⟨v₃,(4*(s+t+band+a+b)+21)+(m₂+(2*(s+t+band+a+b)+11)),hu₃.trans (hu₂.trans hu₁),
    Nat.add_le_add_left (Nat.add_le_add_right hm₂ _) _,Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
