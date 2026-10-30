module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPeriodicResidualBoundary

/-! Execute the periodic residual and its solver-order boundary RHS together. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 242 Q A U}

theorem periodicResidualAndBoundaryData242_exec (hQ : SS.states ≤ Q) {p q w inputExp s t u band a b : ℕ} {α d : ℝ} [NeZero s]
    (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t)
    (C B : ZMod s → GaussianInt)
    (pageTail rhsTail raw : List (Fin (A+4))) (v : HS 242 Q A U) (S : Stacks 168 A) (parent : Stacks 242 A)
    (hview : embStk (Fin.castLE (by decide : 168 ≤ 242)) parent = S)
    (hready : RetainedCouplingReady (2^15*p) q w s t u band a b raw (embStk groupReg (embStk intervalPageReg S)))
    (hsource : S.R 141 = cstream A w (chirpLine s C))
    (hclean : ∀ k ∈ ([107,160] : List (Fin 168)), S.R k = [])
    (hrows : (S.R 140).length = 2*band+1)
    (hpage : S.R 138 = cstream A w (couplingCoefficientPageInterval (2^15*p) q s t u band a b 0 s)++pageTail)
    (hrhs : S.R 93 = cstream A w (packedInterval 0 s B)++rhsTail)
    (h143 : S.R 143 = [])
    (hinputWidth : q+inputExp+2 ≤ w)
    (hC : ∀ j ∈ (if false then haloBoundary s t band a b else haloInterior s t band a b),
      ‖value q (C j)‖ ≤ (2 : ℝ)^inputExp)
    (hp : 0 < p) (hαu : α^2 = (u : ℝ)) (hθ : 0 < (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hCoeffWidth : q+(8*p+1)+2 ≤ w)
    (V : ℕ) (h166 : S.R 166 = [])
    (h139 : (S.R 139).length = (couplingCoefficientPageInterval (2^15*p) q s t u band a b 0 s).length)
    (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (hwide : 8*(t+1)^2+4*band+8 < 2^V)
    (hfitV : 0+(s+2*band)+s < 2^V)
    (hV : (S.R 163).length = V)
    (hbase : ∀ k ∈ [(145 : Fin 168),146,147,149,151,155,165],
      S.R k = binSyms V (couplingIntervalValue s t band a b 0 s k))
    (hderived : ∀ k ∈ [(148 : Fin 168),154,156,164], S.R k = [])
    (h158 : S.R 158 = []) (h135 : S.R 135 = []) (h167 : S.R 167 = []) (hwidth : (S.R 130).length = w) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (2*((s+2*band)*w)+2)+((padCouplingSourceCost s band w+4*((s+2*band)*w)+4)+(36*V+36+(((8*s+8*band+11*V+12+(152*V+153+((32*(s+2*band)+2)*tblC V 1+68*V+2*(s+2*band)+72)+maskCouplingSourceCost (s+2*band) w)) +
        (12*((s+2*band)*w)+17*s+26*band+11*V+24) +
        (144*V+145+((46*s+2)*tblC V 1+66*V+2*s+70)+(6*s+11*V+6+(retainedPageSpatialIntervalLoopCost false q w s t band a b 0 s+
        (22*s+22*V+22+transferCountedLineCost s w+
          transferCountedLineCost (couplingCoefficientPageInterval (2^15*p) q s t u band a b 0 s).length w))))) + (28*s*w+36*s+11*V+26))))+packedBoundaryDataCost V s (haloBoundary s t band a b).card w ∧
      Exec body (embProg (Fin.castLE (by decide : 168 ≤ 242)) Empty.elim (.seq (.seq (.seq prepareFullLineRibbon (completedGatheredFeedCouplingInterval hQ false))
        (uclear 160)) packedBoundaryData)) (mk v parent) m
        (mk v' (embOvr (Fin.castLE (by decide : 168 ≤ 242)) (periodicBoundaryResult S V s t band a b w
          (guardedCouplingRowField (2^15*p) q t u band a b false C B)
          (couplingRowField (2^15*p) q t u band a b false C B) rhsTail).get parent)) := by
  let e : Fin 168 → Fin 242 := Fin.castLE (by decide)
  have hinj : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun k : Fin 242 => k.val) hij
  obtain ⟨vi,n,hu,hn,he⟩ := periodicResidualAndBoundaryData_exec
    (body := fun f : Empty => nomatch f) hQ hA hw5 hqw hst C B pageTail rhsTail raw
    (embDn e v) S hready hsource hclean hrows hpage hrhs h143 hinputWidth hC hp hαu hθ hgap hbudget
    hCoeffWidth V h166 h139 haS hbS hbandS hwide hfitV hV hbase hderived h158 h135 h167 hwidth
  obtain ⟨v',hv,hu',he'⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    hinj (fun f => nomatch f) he v rfl parent hview
  exact ⟨v',n,hu'.trans hu,hn,he'⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
