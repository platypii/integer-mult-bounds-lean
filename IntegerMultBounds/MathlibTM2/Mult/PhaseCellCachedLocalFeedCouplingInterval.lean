module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedLocalCouplingInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLocalFeedCouplingInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFeedPackedCouplingResult
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingIntervalMetadata

/-! The local interval coupling lifecycle feeds the next solve directly.
It releases the reversed intermediate and restores its borrowed output suffix. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {Q A : ℕ} {U : Type} {body : Empty → Pr Empty 168 Q A U}

noncomputable def cachedLocalFeedCouplingInterval (hQ : SS.states ≤ Q) : Pr Empty 168 Q A U :=
  .seq (cachedLocalCouplingInterval hQ) feedPackedCouplingResult

theorem cachedLocalFeedCouplingInterval_exec_within (hQ : SS.states ≤ Q) {P q w s t u band a b origin N : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t)
    (C B : ZMod s → GaussianInt)
    (hfit : origin+N ≤ s)
    (tail pageTail rhsTail raw : List (Fin (A+4)))
    (K : ℕ) (hpush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ K) (v : HS 168 Q A U) (S : Stacks 168 A)
    (hready : RetainedCouplingReady P q w s t u band a b raw (embStk groupReg (embStk intervalPageReg S)))
    (hlocalOrigin : origin = a) (hlocalEnd : b = a+N) (hsep : N+band ≤ s)
    (hsource : S.R 132 = cstream A w (packedInterval a N C)++tail) (h127 : S.R 127 = [])
    (hrows : (S.R 140).length = 2*band+1)
    (hpage : S.R 138 = cstream A w (couplingCoefficientPageInterval P q s t u band a b origin N)++pageTail)
    (hrhs : S.R 93 = cstream A w (packedInterval origin N B)++rhsTail)
    (h143 : S.R 143 = [])
    (hCfits : ∀ j, Fits w (C j))
    (has : ∀ j < N, ∀ z ∈ couplingCoefficientWords P q s t u band (origin+j), Fits w z ∧ z.im = 0)
    (V : ℕ) (hNV : N < 2^V) (h165 : S.R 165 = binSyms V N) (h166 : S.R 166 = [])
    (h139 : (S.R 139).length = (couplingCoefficientPageInterval P q s t u band a b origin N).length)
    (hbS : b ≤ s) (hbandS : band ≤ s)
    (h159 : S.R 159 = (couplingRibbonFlags (s := s) boundary t band a b origin N).map
      (fun flag => pairSym A flag flag))
    (h161 : S.R 161 = recoveryGuardIntervalSymbols true A s t (2*band) a b origin N)
    (h158 : S.R 158 = []) (h135 : S.R 135 = []) (h167 : S.R 167 = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (((16*N*w+21*N+14*band*w+13*band+11*V+46)+cachedGatheredRibbonCost (N+2*band) w+(12*((N+2*band)*w)+11*(N+2*band)+14)) +
        (12*((N+2*band)*w)+17*N+26*band+11*V+24) +
        ((6*N+6)+(6*N+11*V+6+(retainedPageSpatialIntervalLoopCost boundary q w s t band a b origin N+
        (22*N+22*V+22+transferCountedLineCost N w+
          transferCountedLineCost (couplingCoefficientPageInterval P q s t u band a b origin N).length w))))) + (28*N*w+36*N+11*V+26) ∧
      ∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(cachedLocalCouplingWorkspace (Q := Q) (A := A) (U := U) P K q w s t u band a b origin N V+mnProgPush (feedPackedCouplingResult (P₀ := Empty) (Q := Q) (A := A) (U := U))*(28*N*w+36*N+11*V+26)))
        depth (cachedLocalFeedCouplingInterval hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 93 rhsTail) 110
          (cstream A w (packedInterval origin N (guardedCouplingRowField P q t u band a b boundary C B))++S.R 110))}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := cachedLocalCouplingInterval_exec_within (body := body)
    hQ boundary hA hw5 hqw hst C B hfit tail pageTail rhsTail raw K hpush v S
    hready hlocalOrigin hlocalEnd hsep hsource h127 hrows hpage hrhs h143
    (fun j _ => couplingInputWords_fits boundary t band a b (origin+j) w C hCfits) has V hNV h165 h166 h139
    hbS hbandS h159 h161 h158 h135 h167
  let ys := packedInterval origin N (guardedCouplingRowField P q t u band a b boundary C B)
  let G : Stacks 168 A := {S with R := (Function.update (Function.update S.R 93 rhsTail) 113
    (cstream A w ys.reverse++S.R 113))}
  have hfresh : ∀ r ∈ [(0 : Fin 168),1,2,104,105,106,108,109,115], G.R r = [] := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [G,embStk,groupReg,intervalPageReg] using hready.low 0 (by decide)
    · simpa [G,embStk,groupReg,intervalPageReg] using hready.low 1 (by decide)
    · simpa [G,embStk,groupReg,intervalPageReg] using hready.low 2 (by decide)
    all_goals first
    | simpa [G,embStk,groupReg,intervalPageReg] using hready.fresh 104 (by simp)
    | simpa [G,embStk,groupReg,intervalPageReg] using hready.fresh 105 (by simp)
    | simpa [G,embStk,groupReg,intervalPageReg] using hready.fresh 106 (by simp)
    | simpa [G,embStk,groupReg,intervalPageReg] using hready.fresh 108 (by simp)
    | simpa [G,embStk,groupReg,intervalPageReg] using hready.fresh 109 (by simp)
    | simpa [G,embStk,groupReg,intervalPageReg] using hready.fresh 115 (by simp)
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := feedPackedCouplingResult_exec (body := body) V N w hNV ys
    (packedInterval_length _ hfit) (S.R 113) v₁ G
    (by simpa [G] using h165) (by simpa [G] using h166)
    (by simpa [G,embStk,groupReg,intervalPageReg] using hready.width) (by simp [G]) hfresh
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,by omega,?_⟩
  intro depth
  have ht₂ := mn_native_exec_within he₂ (mnProgPush (feedPackedCouplingResult (P₀ := Empty) (Q := Q) (A := A) (U := U))) (WordCmd.empty_native _) depth
    (mnSize (mk v₁ G)+depth+mnProgPush (feedPackedCouplingResult (P₀ := Empty) (Q := Q) (A := A) (U := U))*(28*N*w+36*N+11*V+26))
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ hm₂) _)
  refine (mn_seq_within_add (a := cachedLocalCouplingWorkspace (Q := Q) (A := A) (U := U) P K q w s t u band a b origin N V) (b := mnProgPush (feedPackedCouplingResult (P₀ := Empty) (Q := Q) (A := A) (U := U))*(28*N*w+36*N+11*V+26)) (he₁ depth) ht₂).cast rfl ?_
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext r
  by_cases h1 : r = 93 <;> by_cases h2 : r = 113 <;> by_cases h3 : r = 110 <;>
    simp [G,ys,h1,h2,h3]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
