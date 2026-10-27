module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSpatialCouplingRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOuterWorkspace

/-! Generate the whole-line row clock, execute every coupling row and publish
in natural coordinate order, releasing the clock and current index. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def runCouplingRows (hQ : SS.states ≤ Q) (boundary : Bool) : Pr P₀ 144 Q A U :=
  spatialCouplingRows hQ boundary

def runCouplingRowsCost (boundary : Bool) (P q w s t u band a b : ℕ) : ℕ :=
  spatialCouplingGuardedRowsCost boundary P q w s t u band a b

theorem runCouplingRows_exec (hQ : SS.states ≤ Q) {P q w s t u band a b : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s) (hP : 13 ≤ P)
    (C : ZMod s → GaussianInt) (rhs : List GaussianInt) (hlen : rhs.length = s)
    (tail rhsTail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b (cstream A w (chirpLine s C)++tail) (embStk groupReg S))
    (hindex : S.R 107 = []) (hrhs : S.R 93 = cstream A w rhs++rhsTail)
    (h143 : S.R 143 = []) (h135 : S.R 135 = [])
    (hxs : ∀ j < s, ∀ x ∈ couplingInputWords boundary t band a b j C, Fits w x)
    (has : ∀ j < s, ∀ z ∈ couplingCoefficientWords P q s t u band j, Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧ m ≤ runCouplingRowsCost boundary P q w s t u band a b ∧
      Exec (embTab groupReg body) (runCouplingRows hQ boundary) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 93 rhsTail)
          113 (cstream A w (guardedCouplingRowWords P q t u band a b boundary C 0 rhs)++S.R 113))}) := by
  exact spatialCouplingRows_exec (body := embTab groupReg body) hQ boundary hA hw5 hqw
    hst haS hbS hbandS hP C rhs hlen tail rhsTail v S hready hindex hrhs h143 h135 hxs has

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
