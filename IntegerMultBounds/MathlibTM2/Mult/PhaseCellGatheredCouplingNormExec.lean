module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCompletedGatheredFeedCouplingInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingInputAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingCoefficientAccuracy

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 168 Q A U}

theorem completedGatheredFeedCouplingInterval_norm_exec (hQ : SS.states ≤ Q) {p q w inputExp s t u band a b origin N : ℕ} {α d : ℝ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t)
    (C B : ZMod s → GaussianInt)
    (hfit : origin+N ≤ s)
    (tail pageTail rhsTail raw : List (Fin (A+4))) (v : HS 168 Q A U) (S : Stacks 168 A)
    (hready : RetainedCouplingReady (2^15*p) q w s t u band a b raw (embStk groupReg (embStk intervalPageReg S)))
    (hsource : S.R 160 = cstream A w (rawCouplingRibbon band origin N C)++tail)
    (hrows : (S.R 140).length = 2*band+1)
    (hpage : S.R 138 = cstream A w (couplingCoefficientPageInterval (2^15*p) q s t u band a b origin N)++pageTail)
    (hindex : (S.R 107).length = origin) (hrhs : S.R 93 = cstream A w (packedInterval origin N B)++rhsTail)
    (h143 : S.R 143 = [])
    (hinputWidth : q+inputExp+2 ≤ w)
    (hC : ∀ j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b),
      ‖value q (C j)‖ ≤ (2 : ℝ)^inputExp)
    (hp : 0 < p) (hαu : α^2 = (u : ℝ)) (hθ : 0 < (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hCoeffWidth : q+(8*p+1)+2 ≤ w)
    (V : ℕ) (h166 : S.R 166 = [])
    (h139 : (S.R 139).length = (couplingCoefficientPageInterval (2^15*p) q s t u band a b origin N).length)
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
          transferCountedLineCost (couplingCoefficientPageInterval (2^15*p) q s t u band a b origin N).length w))))) + (28*N*w+36*N+11*V+26)) ∧
      Exec body (completedGatheredFeedCouplingInterval hQ boundary) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (completedCouplingIntervalR S.R V band origin N) 93 rhsTail) 110
          (cstream A w (packedInterval origin N (guardedCouplingRowField (2^15*p) q t u band a b boundary C B))++S.R 110))}) := by
  exact completedGatheredFeedCouplingInterval_exec (body := body) hQ boundary hA hw5 hqw hst C B hfit
    tail pageTail rhsTail raw v S hready hsource hrows hpage hindex hrhs h143
    (fun j _ => couplingInputWords_fits_of_norm boundary t band a b (origin+j) C hinputWidth hC)
    (fun j _ => fun z hz => (couplingCoefficientWords_fits hp (NeZero.pos s) hst hαu hθ hgap hbudget hCoeffWidth z hz))
    V h166 h139 haS hbS hbandS hwide hfitV hV hbase hderived h158 h135 h167

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
