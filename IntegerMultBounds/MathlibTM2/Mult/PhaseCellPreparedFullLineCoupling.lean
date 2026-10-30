module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFullLineRibbon
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGatheredCouplingNormExec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingInputAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingCoefficientAccuracy

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 168 Q A U}

def fullLineRibbonBank {A s : ℕ} [NeZero s] (C : ZMod s → GaussianInt) (band w : ℕ)
    (S : Stacks 168 A) : Stacks 168 A :=
  {S with R := (Function.update (Function.update S.R 141 [])
    160 (cstream A w (rawCouplingRibbon band 0 s C)))}

/-- Final owned metadata and residual, after disposing the cyclic source. -/
def fullLineCouplingResult {A : ℕ} (S : Stacks 168 A) (V band s : ℕ)
    (residual rhsTail : List (Fin (A+4))) : Stacks 168 A :=
  {S with R := (Function.update (Function.update (Function.update
    (completedCouplingIntervalR (Function.update S.R 141 []) V band 0 s) 93 rhsTail)
    110 (residual++S.R 110)) 160 [])}

@[simp] theorem fullLineCouplingResult_source {A : ℕ} (S : Stacks 168 A) (V band s : ℕ)
    (residual rhsTail : List (Fin (A+4))) :
    (fullLineCouplingResult S V band s residual rhsTail).R 110 = residual++S.R 110 := by
  simp [fullLineCouplingResult]

@[simp] theorem fullLineCouplingResult_ribbon {A : ℕ} (S : Stacks 168 A) (V band s : ℕ)
    (residual rhsTail : List (Fin (A+4))) :
    (fullLineCouplingResult S V band s residual rhsTail).R 160 = [] := by
  simp [fullLineCouplingResult]

/-- Periodic source disposal leaves the completed geometry ready for boundary selection. -/
theorem fullLineCouplingResult_metadata {A V s t band a b : ℕ} (S : Stacks 168 A)
    (residual rhsTail : List (Fin (A+4))) (hV : (S.R 163).length = V)
    (hbase : ∀ k ∈ [(145 : Fin 168),146,147,149,151,155,165],
      S.R k = binSyms V (couplingIntervalValue s t band a b 0 s k)) :
    CouplingIntervalMetadata V s t band a b 0 s (fullLineCouplingResult S V band s residual rhsTail) := by
  constructor
  · simpa [fullLineCouplingResult,completedCouplingIntervalR] using hV
  · intro k hk
    simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
    | (simp [fullLineCouplingResult,completedCouplingIntervalR,couplingIntervalValue]; done)
    | simpa [fullLineCouplingResult,completedCouplingIntervalR] using hbase _ (by simp)

theorem preparedFullLineCoupling_exec (hQ : SS.states ≤ Q) {p q w inputExp s t u band a b : ℕ} {α d : ℝ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
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
    (hC : ∀ j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b),
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
    (h158 : S.R 158 = []) (h135 : S.R 135 = []) (h167 : S.R 167 = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (2*((s+2*band)*w)+2)+((padCouplingSourceCost s band w+4*((s+2*band)*w)+4)+(36*V+36+(((8*s+8*band+11*V+12+(152*V+153+((32*(s+2*band)+2)*tblC V 1+68*V+2*(s+2*band)+72)+maskCouplingSourceCost (s+2*band) w)) +
        (12*((s+2*band)*w)+17*s+26*band+11*V+24) +
        (144*V+145+((46*s+2)*tblC V 1+66*V+2*s+70)+(6*s+11*V+6+(retainedPageSpatialIntervalLoopCost boundary q w s t band a b 0 s+
        (22*s+22*V+22+transferCountedLineCost s w+
          transferCountedLineCost (couplingCoefficientPageInterval (2^15*p) q s t u band a b 0 s).length w))))) + (28*s*w+36*s+11*V+26)))) ∧
      Exec body (.seq (.seq prepareFullLineRibbon (completedGatheredFeedCouplingInterval hQ boundary)) (uclear 160)) (mk v S) m
        (mk v' (fullLineCouplingResult S V band s
          (cstream A w (packedInterval 0 s (guardedCouplingRowField (2^15*p) q t u band a b boundary C B))) rhsTail)) ∧
      CouplingIntervalMetadata V s t band a b 0 s (fullLineCouplingResult S V band s
        (cstream A w (packedInterval 0 s (guardedCouplingRowField (2^15*p) q t u band a b boundary C B))) rhsTail) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hr⟩ := prepareFullLineRibbon_exec (body := body) C band w hbandS v S
    hsource hclean raw hready
  let K := fullLineRibbonBank C band w S
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := completedGatheredFeedCouplingInterval_norm_exec (body := body)
    hQ boundary hA hw5 hqw hst C B (by omega) [] pageTail rhsTail raw v₁ K hr
    (by simp [K,fullLineRibbonBank])
    (by simpa [K,fullLineRibbonBank] using hrows)
    (by simpa [K,fullLineRibbonBank] using hpage)
    (by simp [K,fullLineRibbonBank,hclean 107 (by simp)])
    (by simpa [K,fullLineRibbonBank] using hrhs)
    (by simpa [K,fullLineRibbonBank] using h143)
    hinputWidth hC hp hαu hθ hgap hbudget hCoeffWidth V
    (by simpa [K,fullLineRibbonBank] using h166)
    (by simpa [K,fullLineRibbonBank] using h139) haS hbS hbandS hwide hfitV
    (by simpa [K,fullLineRibbonBank] using hV)
    (by intro k hk; have hn : k ≠ 141 ∧ k ≠ 160 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        simpa [K,fullLineRibbonBank,hn.1,hn.2] using hbase k hk)
    (by intro k hk; have hn : k ≠ 141 ∧ k ≠ 160 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; rcases hk with rfl | rfl | rfl | rfl <;> decide
        simpa [K,fullLineRibbonBank,hn.1,hn.2] using hderived k hk)
    (by simpa [K,fullLineRibbonBank] using h158)
    (by simpa [K,fullLineRibbonBank] using h135)
    (by simpa [K,fullLineRibbonBank] using h167)
  let G : Stacks 168 A := {S with R := (Function.update (Function.update (completedCouplingIntervalR (fullLineRibbonBank C band w S).R V band 0 s) 93 rhsTail) 110
          (cstream A w (packedInterval 0 s (guardedCouplingRowField (2^15*p) q t u band a b boundary C B))++S.R 110))}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) 160 v₂ G
  have hlen : (G.R 160).length = (s+2*band)*w := by
    simp [G,fullLineRibbonBank,completedCouplingIntervalR,length_cstream,rawCouplingRibbon_fullLine,
      IntegerMultBounds.NLogN.PhaseCellMatrix.cyclicPaddedLine]
  refine ⟨v₃,(n₁+n₂)+(2*(G.R 160).length+2),hu₃.trans (hu₂.trans hu₁),?_,?_,?_⟩
  · rw [hlen]
    omega
  · have he : Exec body (.seq prepareFullLineRibbon (completedGatheredFeedCouplingInterval hQ boundary))
        (mk v S) (n₁+n₂) (mk v₂ G) := by
      simpa [G,K,fullLineRibbonBank] using Exec.seq he₁ he₂
    refine (Exec.seq he he₃).cast rfl ?_
    apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp only [G,fullLineCouplingResult,fullLineRibbonBank,completedCouplingIntervalR,Function.update_apply]
    split_ifs <;> subst_vars <;> rfl
  · exact fullLineCouplingResult_metadata S _ _ hV hbase

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
