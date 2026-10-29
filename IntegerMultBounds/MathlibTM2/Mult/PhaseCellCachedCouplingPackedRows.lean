module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedCouplingRowLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCouplingRowField
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop

/-! Counted consecutive residual/recovery rows with exact physical stream and frame. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

theorem cachedCouplingPackedRows_exec (hQ : SS.states ≤ Q) {P q w s t u band a b i : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s) (hP : 13 ≤ P)
    (C : ZMod s → GaussianInt) (B : ZMod s → GaussianInt) (L : ℕ) (hfit : i+L ≤ s)
    (tail rhsTail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b (cstream A w (chirpLine s C)++tail) (embStk cachedCouplingCoreReg (embStk cachedCouplingOuterReg S)))
    (hcache : ∃ cacheTail, S.R 141 = cstream A w (chirpLine s C)++cacheTail)
    (hindex : (S.R 107).length = i) (hrhs : S.R 93 = cstream A w (packedInterval i L B)++rhsTail)
    (hcount : (S.R 143).length = L)
    (hxs : ∀ j < L, ∀ x ∈ couplingInputWords boundary t band a b (i+j) C, Fits w x)
    (has : ∀ j < L, ∀ z ∈ couplingCoefficientWords P q s t u band (i+j), Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧ m ≤ cachedCouplingRowLoopCost P q w s t u band a b i L ∧
      Exec (body) (cachedCouplingRowLoop hQ boundary) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          93 rhsTail) 107 (List.replicate L tick++S.R 107))
          113 (cstream A w (packedInterval i L (couplingRowField P q t u band a b boundary C B)).reverse++S.R 113)) 143 [])}) := by
  have he := cachedCouplingRowLoop_exec (body := body) hQ boundary hA hw5 hqw hst haS hbS hbandS hP
    C (packedInterval i L B) (by simpa only [packedInterval_length B hfit] using hfit)
    tail rhsTail v S hready hcache hindex hrhs
    (by simpa only [packedInterval_length B hfit] using hcount)
    (by simpa only [packedInterval_length B hfit] using hxs)
    (by simpa only [packedInterval_length B hfit] using has)
  simpa only [packedInterval_length B hfit,couplingRowWords_packed P q t u band a b i L boundary C B hfit] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
