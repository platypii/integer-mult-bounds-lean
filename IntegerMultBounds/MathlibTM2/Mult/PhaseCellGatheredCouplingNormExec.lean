module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCompletedGatheredFeedCouplingInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingInputAccuracy

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 168 Q A U}

theorem completedGatheredFeedCouplingInterval_norm_exec (hQ : SS.states ≤ Q) {P q w inputExp s t u band a b origin N : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t)
    (C B : ZMod s → GaussianInt)
    (hfit : origin+N ≤ s)
    (tail pageTail rhsTail raw : List (Fin (A+4))) (v : HS 168 Q A U) (S : Stacks 168 A)
    (hready : RetainedCouplingReady P q w s t u band a b raw (embStk groupReg (embStk intervalPageReg S)))
    (hsource : S.R 160 = cstream A w (rawCouplingRibbon band origin N C)++tail)
    (hrows : (S.R 140).length = 2*band+1)
    (hpage : S.R 138 = cstream A w (couplingCoefficientPageInterval P q s t u band a b origin N)++pageTail)
    (hindex : (S.R 107).length = origin) (hrhs : S.R 93 = cstream A w (packedInterval origin N B)++rhsTail)
    (h143 : S.R 143 = [])
    (hinputWidth : q+inputExp+2 ≤ w)
    (hC : ∀ j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b),
      ‖value q (C j)‖ ≤ (2 : ℝ)^inputExp)
    (has : ∀ j < N, ∀ z ∈ couplingCoefficientWords P q s t u band (origin+j), Fits w z ∧ z.im = 0)
    (V : ℕ) (h166 : S.R 166 = [])
    (h139 : (S.R 139).length = (couplingCoefficientPageInterval P q s t u band a b origin N).length)
    (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (hwide : 8*(t+1)^2+4*band+8 < 2^V)
    (hfitV : origin+(N+2*band)+s < 2^V)
    (hV : (S.R 163).length = V)
    (hbase : ∀ k ∈ [(145 : Fin 168),146,147,149,151,155,165],
      S.R k = binSyms V (couplingIntervalValue s t band a b origin N k))
    (hderived : ∀ k ∈ [(148 : Fin 168),154,156,164], S.R k = [])
    (h158 : S.R 158 = []) (h135 : S.R 135 = []) (h167 : S.R 167 = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ 36*V+36+(((8*N+8*band+11*V+12+(152*V+153+((32*(N+2*band)+2)*tblC V 1+68*V+2*(N+2*band)+72)+maskCouplingSourceCost (N+2*band) w)) +
        (12*((N+2*band)*w)+17*N+26*band+11*V+24) +
        (144*V+145+((46*N+2)*tblC V 1+66*V+2*N+70)+(6*N+11*V+6+(retainedPageSpatialIntervalLoopCost boundary q w s t band a b origin N+
        (22*N+22*V+22+transferCountedLineCost N w+
          transferCountedLineCost (couplingCoefficientPageInterval P q s t u band a b origin N).length w))))) + (28*N*w+36*N+11*V+26)) ∧
      Exec body (completedGatheredFeedCouplingInterval hQ boundary) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (completedCouplingIntervalR S.R V band origin N) 93 rhsTail) 110
          (cstream A w (packedInterval origin N (guardedCouplingRowField P q t u band a b boundary C B))++S.R 110))}) := by
  exact completedGatheredFeedCouplingInterval_exec (body := body) hQ boundary hA hw5 hqw hst C B hfit
    tail pageTail rhsTail raw v S hready hsource hrows hpage hindex hrhs h143
    (fun j _ => couplingInputWords_fits_of_norm boundary t band a b (origin+j) C hinputWidth hC)
    has V h166 h139 haS hbS hbandS hwide hfitV hV hbase hderived h158 h135 h167

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
