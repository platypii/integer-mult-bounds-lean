module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRhsMask
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMaskedBoundaryRhs

/-! Ordinary geometry headers generate the mask and the canonical folded boundary RHS. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 148 Q A U}

def generatedBoundaryRhs : Pr P 148 Q A U := .seq boundaryRhsMask maskedBoundaryRhs

def generatedBoundaryRhsCost (s t band a b w : ℕ) : ℕ :=
  closedCouplingSourceMaskCost s t band a b+600*(s+1)*(w+1)

theorem generatedBoundaryRhs_exec {s t band a b : ℕ} [NeZero s]
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hA : 4 ≤ A)
    (C : ZMod s → GaussianInt) (w : ℕ) (tail : List (Fin (A+4))) (v : HS 148 Q A U) (S : Stacks 148 A)
    (hsrc : S.R 110 = cstream A w (chirpLine s C)++tail)
    (hs : (S.R 97).length = s) (ht : (S.R 98).length = t) (hband : (S.R 100).length = band)
    (ha : (S.R 101).length = a) (hb : (S.R 103).length = b)
    (hw : (S.R 94).length = w) (hcount : (S.R 116).length = (haloBoundary s t band a b).card)
    (hfresh : ∀ r ∈ [(106 : Fin 148),108,138,139,143], S.R r = [])
    (hblank : ∀ r : Fin 148, r.val < 77 → S.R r = []) (hleft : ∀ r, S.L r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ generatedBoundaryRhsCost s t band a b w ∧
      Exec body generatedBoundaryRhs (mk v S) m
        (mk v' {S with R := Function.update S.R 143 (cstream A w ((bFoldOrder s (haloBoundary s t band a b)).map C))}) := by
  let mask := couplingSourceMaskSymbols true A s t band a b
  let S₁ : Stacks 148 A := {S with R := Function.update S.R 139 mask}
  let S₂ : Stacks 148 A := {S with R := Function.update S.R 143 (cstream A w ((bFoldOrder s (haloBoundary s t band a b)).map C))}
  have prepare : Runs body boundaryRhsMask S S₁ (closedCouplingSourceMaskCost s t band a b) := by
    intro vi
    exact boundaryRhsMask_exec hst haS hbS hA vi S hs ht hband ha hb
      (hfresh 138 (by simp)) (hfresh 139 (by simp)) (hfresh 106 (by simp)) (hfresh 108 (by simp))
      (fun r hr => hblank r (by omega))
  have gather : Runs body maskedBoundaryRhs S₁ S₂ (600*(s+1)*(w+1)) := by
    intro vi
    obtain ⟨vf,m,hu,hm,he⟩ := maskedBoundaryRhs_exec (body := body) hst hA band a b hbS C w tail vi S₁
      (by simpa [S₁] using hsrc) (by simp [S₁,mask]) (by simpa [S₁] using hw)
      (by simpa [S₁] using hcount) (by simpa [S₁] using hfresh 143 (by simp))
      (by simpa [S₁] using hfresh 106 (by simp))
      (by intro r hr; have hn : r ≠ 139 := by intro hh; subst r; norm_num at hr
          simpa [S₁,hn] using hblank r hr) hleft
    refine ⟨vf,m,hu,hm,he.cast rfl ?_⟩
    apply congrArg (mk vf)
    refine Stacks.ext rfl rfl rfl ?_
    funext r
    by_cases h139 : r = 139
    · subst r; simp [S₁,S₂,hfresh 139 (by simp)]
    simp [S₁,S₂,h139,Function.update_apply]
  exact (prepare.seq gather) v

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
