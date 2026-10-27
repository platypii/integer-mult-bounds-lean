module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPageSpatialCouplingRowLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRunGeneratedRetainedPageCouplingRows

/-! Generate the whole-line row clock, execute every coupling row and publish
in natural coordinate order, releasing the clock and current index. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

/- Earlier per-row counter setup: restore commit 1e996ef0. -/
noncomputable def runPreparedPageCouplingRows (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  runGeneratedRetainedPageCouplingRows hQ

def runPreparedPageCouplingRowsCost (boundary : Bool) (q w s t band a b Nwords : ℕ) : ℕ :=
  runGeneratedRetainedPageCouplingRowsCost boundary q w s t band a b Nwords

theorem runPreparedPageCouplingRows_exec (hQ : SS.states ≤ Q) {P q w s t u band a b : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t)
    (C : ZMod s → GaussianInt) (rhs : List GaussianInt) (hlen : rhs.length = s)
    (tail pageTail maskTail rhsTail raw : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b raw (embStk groupReg S))
    (hsource : S.R 141 = cstream A w (cyclicPaddedLine (fun j : ZMod s =>
      if j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
      then C j else 0) band)++tail)
    (hmask : S.R 136 = couplingGuardSymbols boundary A s t band a b++maskTail)
    (hindex : S.R 107 = []) (hrhs : S.R 93 = cstream A w rhs++rhsTail)
    (h143 : S.R 143 = [])
    (hrows : (S.R 140).length = 2*band+1)
    (hpage : S.R 138 = cstream A w (couplingCoefficientPage P q s t u band a b s)++pageTail)
    (hwordCount : (S.R 139).length = (couplingCoefficientPage P q s t u band a b s).length)
    (hxs : ∀ j < s, ∀ x ∈ couplingInputWords boundary t band a b j C, Fits w x)
    (has : ∀ j < s, ∀ z ∈ couplingCoefficientWords P q s t u band j, Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧ m ≤ runPreparedPageCouplingRowsCost boundary q w s t band a b
      (couplingCoefficientPage P q s t u band a b s).length ∧
      Exec (body) (runPreparedPageCouplingRows hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 136 maskTail) 93 rhsTail)
          113 (cstream A w (guardedCouplingRowWords P q t u band a b boundary C 0 rhs)++S.R 113))}) := by
  exact runGeneratedRetainedPageCouplingRows_exec (body := body) hQ boundary hA hw5 hqw hst C rhs hlen
    tail pageTail maskTail rhsTail raw v S hready hsource hmask hindex hrhs h143 hrows hpage hwordCount hxs has

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
