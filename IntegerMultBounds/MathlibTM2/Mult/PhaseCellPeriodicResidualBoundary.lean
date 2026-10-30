module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPeriodicBoundaryData

/-! Execute the periodic residual and its solver-order boundary RHS together. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 168 Q A U}

def periodicBoundaryResult {A s : ℕ} [NeZero s] (S : Stacks 168 A) (V s' t band a b w : ℕ)
    (D E : ZMod s → GaussianInt) (rhsTail : List (Fin (A+4))) : Stacks 168 A :=
  let R := fullLineCouplingResult S V band s' (cstream A w (packedInterval 0 s' D)) rhsTail
  {R with R := (Function.update (Function.update (Function.update R.R
    167 (couplingSourceIntervalMaskSymbols true A s t band a b 0 s'))
    116 (List.replicate (haloBoundary s t band a b).card tick))
    143 (cstream A w ((bFoldOrder s (haloBoundary s t band a b)).map E)))}

/-- The boundary solver receives its actual count and folded RHS together. -/
theorem periodicBoundaryResult_data {A s : ℕ} [NeZero s] (S : Stacks 168 A)
    (V s' t band a b w : ℕ) (D E : ZMod s → GaussianInt) (rhsTail : List (Fin (A+4))) :
    let R := periodicBoundaryResult S V s' t band a b w D E rhsTail
    (R.R 116).length = (haloBoundary s t band a b).card ∧
      R.R 143 = cstream A w ((bFoldOrder s (haloBoundary s t band a b)).map E) := by
  simp [periodicBoundaryResult]

/-- Every tape outside the explicit residual/metadata footprint is preserved. -/
theorem periodicBoundaryResult_frame {A s : ℕ} [NeZero s] (S : Stacks 168 A)
    (V s' t band a b w : ℕ) (D E : ZMod s → GaussianInt) (rhsTail : List (Fin (A+4)))
    (k : Fin 168) (hk : k ∉ ([93,110,116,141,143,148,154,156,160,164,167] : List (Fin 168))) :
    (periodicBoundaryResult S V s' t band a b w D E rhsTail).R k = S.R k := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hk
  rcases hk with ⟨h93,h110,h116,h141,h143,h148,h154,h156,h160,h164,h167⟩
  simp [periodicBoundaryResult,fullLineCouplingResult,completedCouplingIntervalR,
    h93,h110,h116,h141,h143,h148,h154,h156,h160,h164,h167]

theorem periodicResidualAndBoundaryData_exec (hQ : SS.states ≤ Q) {p q w inputExp s t u band a b : ℕ} {α d : ℝ} [NeZero s]
    (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t)
    (C B : ZMod s → GaussianInt)
    (pageTail rhsTail raw : List (Fin (A+4))) (v : HS 168 Q A U) (S : Stacks 168 A)
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
      Exec body (.seq (.seq (.seq prepareFullLineRibbon (completedGatheredFeedCouplingInterval hQ false))
        (uclear 160)) packedBoundaryData) (mk v S) m
        (mk v' (periodicBoundaryResult S V s t band a b w
          (guardedCouplingRowField (2^15*p) q t u band a b false C B)
          (couplingRowField (2^15*p) q t u band a b false C B) rhsTail)) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,_⟩ := preparedFullLineCoupling_exec (body := body) hQ false hA hw5 hqw
    hst C B pageTail rhsTail raw v S hready hsource hclean hrows hpage hrhs h143 hinputWidth hC
    hp hαu hθ hgap hbudget hCoeffWidth V h166 h139 haS hbS hbandS hwide hfitV hV hbase hderived h158 h135 h167
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := periodicResidualBoundaryData_exec (body := body) v₁ S C B rhsTail raw
    hready hV hbase hst haS hbS (by omega) (by omega) (by simpa using hfitV) hwidth h167 h143
  exact ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
