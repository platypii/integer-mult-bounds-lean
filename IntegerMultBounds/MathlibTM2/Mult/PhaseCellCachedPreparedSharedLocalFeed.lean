module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedCouplingCounters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedSharedLocalFeedCouplingInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedSharedLocalFeedCouplingInterval
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingReadinessStock

/-! Generate private scalar counters, execute local coupling through retained
master headers, then release the counters. All masters and scratch are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {Q A : ℕ} {U : Type} {body : Empty → Pr Empty 168 Q A U}

noncomputable def cachedPreparedSharedLocalFeedCouplingWorkspace
    (P M q w s t u band a b origin N V : ℕ) : ℕ :=
  (3*(prepareCost q w+6*q+4*band+10)+(cachedLocalCouplingWorkspace (Q := Q) (A := A) (U := U) P M q w s t u band a b origin N V+mnProgPush (feedPackedCouplingResult (P₀ := Empty) (Q := Q) (A := A) (U := U))*(28*N*w+36*N+11*V+26)))

def cachedPreparedSharedLocalFeedCouplingIntervalCost (boundary : Bool)
    (P q w s t u band a b origin N V : ℕ) : ℕ :=
  (prepareCost q w+6*q+4*band+10)+((((16*N*w+21*N+14*band*w+13*band+11*V+46)+cachedGatheredRibbonCost (N+2*band) w+(12*((N+2*band)*w)+11*(N+2*band)+14)) +
        (12*((N+2*band)*w)+17*N+26*band+11*V+24) +
        ((6*N+6)+(6*N+11*V+6+(retainedPageSpatialIntervalLoopCost boundary q w s t band a b origin N+
        (22*N+22*V+22+transferCountedLineCost N w+
          transferCountedLineCost (couplingCoefficientPageInterval P q s t u band a b origin N).length w))))) + (28*N*w+36*N+11*V+26))+2*(w+q+Schoenhage.Schedule.topN w)+7

noncomputable def cachedPreparedSharedLocalFeedCouplingInterval (hQ : SS.states ≤ Q) : Pr Empty 168 Q A U :=
  .seq sharedCouplingCounters
    (.seq (cachedSharedLocalFeedCouplingInterval hQ) (clearWords sharedCouplingCounterPorts))

theorem cachedPreparedSharedLocalFeedCouplingInterval_exec_within (hQ : SS.states ≤ Q) {P q w s t u band a b origin N : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t)
    (C B : ZMod s → GaussianInt)
    (hfit : origin+N ≤ s)
    (tail pageTail rhsTail raw : List (Fin (A+4)))
    (M : ℕ) (hpush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ M) (v : HS 168 Q A U) (S : Stacks 168 A)
    (hready : CouplingReady P q w s t u band a b raw (embStk sharedCouplingCoreReg S))
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
      m ≤ cachedPreparedSharedLocalFeedCouplingIntervalCost boundary P q w s t u band a b origin N V ∧
      ∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          cachedPreparedSharedLocalFeedCouplingWorkspace (Q := Q) (A := A) (U := U)
            P M q w s t u band a b origin N V)
        depth (cachedPreparedSharedLocalFeedCouplingInterval hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 93 rhsTail) 110
          (cstream A w (packedInterval origin N (guardedCouplingRowField P q t u band a b boundary C B))++S.R 110))}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁,hreadyK⟩ := sharedCouplingCounters_exec (body := body) hw5 hqw raw v S hready
  let K : Stacks 168 A := {S with R := sharedCouplingCountersR q w S.R}
  have hhigh (k : Fin 168) (hk : 97 ≤ k.val) : K.R k = S.R k := sharedCouplingCountersR_high q w S.R k hk
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := cachedSharedLocalFeedCouplingInterval_exec_within (body := body)
    hQ boundary hA hw5 hqw hst C B hfit tail pageTail rhsTail raw M hpush v₁ K hreadyK hlocalOrigin hlocalEnd hsep
    (by rw [hhigh 132 (by decide)]; exact hsource)
    (by rw [hhigh 127 (by decide)]; exact h127)
    (by rw [hhigh 140 (by decide)]; exact hrows)
    (by rw [hhigh 138 (by decide)]; exact hpage)
    (by simpa only [K,sharedCouplingCountersR_rhs] using hrhs)
    (by rw [hhigh 143 (by decide)]; exact h143) hCfits has V hNV
    (by rw [hhigh 165 (by decide)]; exact h165)
    (by rw [hhigh 166 (by decide)]; exact h166)
    (by rw [hhigh 139 (by decide)]; exact h139)
    hbS hbandS
    (by rw [hhigh 159 (by decide)]; exact h159)
    (by rw [hhigh 161 (by decide)]; exact h161)
    (by rw [hhigh 158 (by decide)]; exact h158)
    (by rw [hhigh 135 (by decide)]; exact h135)
    (by rw [hhigh 167 (by decide)]; exact h167)
  let F : Stacks 168 A := {K with R := (Function.update (Function.update K.R 93 rhsTail) 110
    (cstream A w (packedInterval origin N (guardedCouplingRowField P q t u band a b boundary C B))++K.R 110))}
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) sharedCouplingCounterPorts (by decide) v₂ F
  have hsum : (sharedCouplingCounterPorts.map (fun k => (F.R k).length)).sum = w+q+Schoenhage.Schedule.topN w := by
    simp [sharedCouplingCounterPorts,F,K,sharedCouplingCountersR,sharedCouplingCoreReg,sharedCouplingReg,
      packedCellCoreReg,cr,OutputPlacement.code,Nat.add_assoc]
  have hfinal : {F with R := fun k => if k ∈ sharedCouplingCounterPorts then [] else F.R k} =
      {S with R := (Function.update (Function.update S.R 93 rhsTail) 110
        (cstream A w (packedInterval origin N (guardedCouplingRowField P q t u band a b boundary C B))++S.R 110))} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    have hwn := hready.arithmetic CR.wn
    have hpn := hready.arithmetic CR.pn
    have hnn := hready.arithmetic CR.nn
    change S.R (sharedCouplingCoreReg (cr .wn)) = [] at hwn
    change S.R (sharedCouplingCoreReg (cr .pn)) = [] at hpn
    change S.R (sharedCouplingCoreReg (cr .nn)) = [] at hnn
    by_cases hwk : k = sharedCouplingCoreReg (cr .wn)
    · subst k; simpa [F,K,sharedCouplingCountersR,sharedCouplingCounterPorts,sharedCouplingCoreReg,
        sharedCouplingReg,packedCellCoreReg,cr,OutputPlacement.code,Equiv.swap_apply_def] using hwn.symm
    by_cases hpk : k = sharedCouplingCoreReg (cr .pn)
    · subst k; simpa [F,K,sharedCouplingCountersR,sharedCouplingCounterPorts,sharedCouplingCoreReg,
        sharedCouplingReg,packedCellCoreReg,cr,OutputPlacement.code,Equiv.swap_apply_def] using hpn.symm
    by_cases hnk : k = sharedCouplingCoreReg (cr .nn)
    · subst k; simpa [F,K,sharedCouplingCountersR,sharedCouplingCounterPorts,sharedCouplingCoreReg,
        sharedCouplingReg,packedCellCoreReg,cr,OutputPlacement.code,Equiv.swap_apply_def] using hnn.symm
    by_cases h93 : k = 93
    · subst k
      simp [F,K,sharedCouplingCounterPorts,sharedCouplingCountersR,sharedCouplingCoreReg,
        sharedCouplingReg,packedCellCoreReg,cr,OutputPlacement.code]
    by_cases h110 : k = 110
    · subst k
      simp [F,K,sharedCouplingCounterPorts,sharedCouplingCountersR,sharedCouplingCoreReg,
        sharedCouplingReg,packedCellCoreReg,cr,OutputPlacement.code]
    simp [F,K,sharedCouplingCounterPorts,sharedCouplingCountersR,hwk,hpk,hnk,h93,h110]
  refine ⟨v₃,m₁+(m₂+(2*(w+q+Schoenhage.Schedule.topN w)+7)),hu₃.trans (hu₂.trans hu₁),(by dsimp only [cachedPreparedSharedLocalFeedCouplingIntervalCost]; omega),
    ?_⟩
  intro depth
  have ht₁ := mn_native_exec_within he₁ 3
    (embProg_native sharedCouplingCoreReg Empty.elim _ couplingReadiness_native) depth
    (mnSize (mk v S)+depth+3*(prepareCost q w+6*q+4*band+10))
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ hm₁) _)
  have ht₃ := mn_native_exec_within he₃ 0 (clearWords_native _) depth
    (mnSize (mk v₂ F)+depth+0) (by simp)
  have ht := mn_seq_within_add (a := 3*(prepareCost q w+6*q+4*band+10)) (b := (cachedLocalCouplingWorkspace (Q := Q) (A := A) (U := U) P M q w s t u band a b origin N V+mnProgPush (feedPackedCouplingResult (P₀ := Empty) (Q := Q) (A := A) (U := U))*(28*N*w+36*N+11*V+26))) ht₁
    ((mn_seq_within_add (a := (cachedLocalCouplingWorkspace (Q := Q) (A := A) (U := U) P M q w s t u band a b origin N V+mnProgPush (feedPackedCouplingResult (P₀ := Empty) (Q := Q) (A := A) (U := U))*(28*N*w+36*N+11*V+26))) (b := 0) (he₂ depth) ht₃).mono (by intro d z hz; simpa only [Nat.add_zero] using hz))
  change ExecWithin body _ depth _ _ _ _
  refine ht.cast ?_ (congrArg (mk v₃) hfinal)
  rw [hsum]
  simp [sharedCouplingCounterPorts]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
