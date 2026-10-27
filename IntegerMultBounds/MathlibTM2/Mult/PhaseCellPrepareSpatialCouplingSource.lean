module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareMaskedCouplingSource
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPadCouplingSource

/-! Prepare the actual masked, cyclically padded source for the complete spatial pass. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def prepareSpatialCouplingSource (boundary : Bool) : Pr P₀ 144 Q A U :=
  .seq (prepareMaskedCouplingSource boundary) padCouplingSource

def prepareSpatialCouplingSourceCost (s t band a b w : ℕ) : ℕ :=
  prepareMaskedCouplingSourceCost s t band a b w+padCouplingSourceCost s band w

theorem prepareSpatialCouplingSource_exec {P q w s t u band a b : ℕ} [NeZero s]
    (boundary : Bool) (hA : 4 ≤ A) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (C : ZMod s → GaussianInt) (tail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b (cstream A w (chirpLine s C)++tail) (embStk groupReg S))
    (h107 : S.R 107 = []) (h135 : S.R 135 = []) (h143 : S.R 143 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareSpatialCouplingSourceCost s t band a b w ∧
      Exec body (prepareSpatialCouplingSource boundary) (mk v S) m
        (mk v' {S with R := Function.update S.R 141 (cstream A w (cyclicPaddedLine (fun j =>
          if j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
          then C j else 0) band)++S.R 141)}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := prepareMaskedCouplingSource_exec (body := body)
    boundary hA hst haS hbS hbandS C tail v S hready h107 h135 h143
  let F := fun j : ZMod s => if j ∈
    (if boundary then haloBoundary s t band a b else haloInterior s t band a b) then C j else 0
  let S₁ : Stacks 144 A := {S with R := Function.update S.R 141 (cstream A w (chirpLine s F)++S.R 141)}
  have hs : (S.R 97).length = s := hready.axis
  have hb : (S.R 100).length = band := hready.bandwidth
  have hw : (S.R 94).length = w := hready.width
  have hf (k : Fin 117) (hk : k ∈ [(92 : Fin 117),96,102,104,105,106,108,109,115,116]) :
      S.R (groupReg k) = [] := hready.fresh k hk
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := padCouplingSource_exec (body := body) F band w hbandS (S.R 141) v₁ S₁
    (by simpa [S₁] using hs) (by simpa [S₁] using hb) (by simpa [S₁] using hw) (by simp [S₁])
    (by simpa [S₁] using h107)
    (by simpa [S₁,groupReg] using hf 108 (by simp)) (by simpa [S₁,groupReg] using hf 109 (by simp))
    (by simpa [S₁,groupReg] using hf 115 (by simp)) (by simpa [S₁,groupReg] using hf 116 (by simp))
    (by simpa [S₁,groupReg] using hf 104 (by simp)) (by simpa [S₁,groupReg] using hf 105 (by simp))
    (by simpa [S₁,groupReg] using hf 106 (by simp))
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,by dsimp only [prepareSpatialCouplingSourceCost]; omega,
    (Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases h141 : k = 141 <;> simp [S₁,F,h141]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
