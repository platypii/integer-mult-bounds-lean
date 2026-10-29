module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedPageSpatialCouplingRowLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedSpatialCouplingInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingCoefficientPageSuffix
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop

/-! Counted consecutive residual/recovery rows with exact physical stream and frame. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

theorem retainedPageSpatialCouplingRowLoop_packed_exec (hQ : SS.states ≤ Q) {P q w s t u band a b origin : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t)
    (C : ZMod s → GaussianInt) (rhs : List GaussianInt)
    (hfit : origin+rhs.length ≤ s)
    (tail pageTail maskTail rhsTail raw : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : RetainedCouplingReady P q w s t u band a b raw (embStk groupReg S))
    (hsource : S.R 141 = cstream A w (couplingSourceInterval boundary t band a b origin rhs.length C)++tail)
    (hrows : (S.R 140).length = 2*band+1)
    (hpage : S.R 138 = cstream A w (couplingCoefficientPageInterval P q s t u band a b origin rhs.length)++pageTail)
    (hmask : S.R 136 = ((couplingGuardSymbols boundary A s t band a b).drop origin).take rhs.length++maskTail)
    (hrhs : S.R 93 = cstream A w rhs++rhsTail)
    (hcount : (S.R 143).length = rhs.length)
    (hxs : ∀ j < rhs.length, ∀ x ∈ couplingInputWords boundary t band a b (origin+j) C, Fits w x)
    (has : ∀ j < rhs.length, ∀ z ∈ couplingCoefficientWords P q s t u band (origin+j), Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧ m ≤ retainedPageSpatialIntervalLoopCost boundary q w s t band a b origin rhs.length ∧
      Exec (body) (retainedPageSpatialCouplingRowLoop hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update S.R 136 maskTail) 138 pageTail) 137
          ((cstream A w (couplingCoefficientPageInterval P q s t u band a b origin rhs.length)).reverse++S.R 137))
          93 rhsTail) 107 (List.replicate rhs.length tick++S.R 107))
          113 (cstream A w (guardedCouplingRowWords P q t u band a b boundary C origin rhs).reverse++S.R 113)) 143 [])
          141 (cstream A w ((couplingSourceInterval boundary t band a b origin rhs.length C).drop rhs.length)++tail))
          142 ((cstream A w ((couplingSourceInterval boundary t band a b origin rhs.length C).take rhs.length)).reverse++S.R 142))}) := by
  apply retainedPageSpatialCouplingRowLoop_interval_exec (body := body) hQ boundary hA hw5 hqw hst C
    (couplingSourceInterval boundary t band a b origin rhs.length C) rhs
    (by rw [couplingSourceInterval_length _ _ _ _ _ _ _ _ hfit]; omega)
    (by intro j hj; exact couplingSourceInterval_window boundary t band a b origin rhs.length j C hfit hj)
    hfit tail pageTail maskTail rhsTail raw v S hready hsource hrows hpage hmask hrhs hcount hxs has

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
