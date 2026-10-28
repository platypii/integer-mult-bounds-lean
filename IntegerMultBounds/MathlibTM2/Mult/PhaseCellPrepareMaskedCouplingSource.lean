module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOuterCouplingSourceMask
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMaskCouplingSource

/-! Generate and apply the original halo mask while preserving the ambient data source. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 144 Q A U}

def prepareMaskedCouplingSource (boundary : Bool) : Pr P 144 Q A U :=
  .seq (outerCouplingSourceMask boundary) maskCouplingSource

def prepareMaskedCouplingSourceCost (s t band a b w : ℕ) : ℕ :=
  closedCouplingSourceMaskCost s t band a b+maskCouplingSourceCost s w

theorem prepareMaskedCouplingSource_exec {P q w s t u band a b : ℕ} [NeZero s]
    (boundary : Bool) (hA : 4 ≤ A) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (C : ZMod s → GaussianInt) (tail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b (cstream A w (chirpLine s C)++tail) (embStk groupReg S))
    (h107 : S.R 107 = []) (h135 : S.R 135 = []) (h143 : S.R 143 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareMaskedCouplingSourceCost s t band a b w ∧
      Exec body (prepareMaskedCouplingSource boundary) (mk v S) m
        (mk v' {S with R := Function.update S.R 141 (cstream A w (chirpLine s (fun j =>
          if j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
          then C j else 0))++S.R 141)}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := outerCouplingSourceMask_exec (body := body) boundary
    hst haS hbS hbandS hA (cstream A w (chirpLine s C)++tail) v S hready
  let S₁ : Stacks 144 A := {S with R := Function.update S.R 109 (couplingSourceMaskSymbols boundary A s t band a b)}
  have hs : (S.R 97).length = s := hready.axis
  have hw : (S.R 94).length = w := hready.width
  have hsrc : S.R 110 = cstream A w (chirpLine s C)++tail := hready.source
  have h108 : S.R 108 = [] := hready.fresh 108 (by simp)
  have h104 : S.R 104 = [] := hready.fresh 104 (by simp)
  have h105 : S.R 105 = [] := hready.fresh 105 (by simp)
  have h109 : S.R 109 = [] := hready.fresh 109 (by simp)
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := maskCouplingSource_halo_exec (body := body) hA boundary t band a b w
    hst hbS C tail v₁ S₁ (by simpa [S₁] using hs) (by simpa [S₁] using hw)
    (by simpa [S₁] using hsrc) (by simp [S₁]) (by simpa [S₁] using h108)
    (by simpa [S₁] using h104) (by simpa [S₁] using h105)
    (by simpa [S₁] using h135) (by simpa [S₁] using h107) (by simpa [S₁] using h143)
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,by dsimp only [prepareMaskedCouplingSourceCost]; omega,
    (Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases h141 : k = 141 <;> by_cases h109' : k = 109 <;>
    simp [S₁,h141,h109',h109]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
