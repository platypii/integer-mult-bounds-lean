module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedCouplingCounters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedLocalFeedCouplingInterval

/-! Generate private scalar counters, execute local coupling through retained
master headers, then release the counters. All masters and scratch are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 168 Q A U}

def sharedCouplingCounterPorts : List (Fin 168) :=
  [sharedCouplingCoreReg (cr .wn),sharedCouplingCoreReg (cr .pn),sharedCouplingCoreReg (cr .nn)]

def preparedSharedLocalFeedCouplingIntervalCost (boundary : Bool)
    (P q w s t u band a b origin N V : ℕ) : ℕ :=
  (prepareCost q w+6*q+4*band+10)+((((16*N*w+21*N+14*band*w+13*band+11*V+46)+(152*V+153+((32*(N+2*band)+2)*tblC V 1+68*V+2*(N+2*band)+72)+maskCouplingSourceCost (N+2*band) w)+(12*((N+2*band)*w)+11*(N+2*band)+14)) +
        (12*((N+2*band)*w)+17*N+26*band+11*V+24) +
        (144*V+145+((46*N+2)*tblC V 1+66*V+2*N+70)+(6*N+11*V+6+(retainedPageSpatialIntervalLoopCost boundary q w s t band a b origin N+
        (22*N+22*V+22+transferCountedLineCost N w+
          transferCountedLineCost (couplingCoefficientPageInterval P q s t u band a b origin N).length w))))) + (28*N*w+36*N+11*V+26))+2*(w+q+Schoenhage.Schedule.topN w)+7

noncomputable def preparedSharedLocalFeedCouplingInterval (hQ : SS.states ≤ Q) (boundary : Bool) : Pr P₀ 168 Q A U :=
  .seq sharedCouplingCounters
    (.seq (sharedLocalFeedCouplingInterval hQ boundary) (clearWords sharedCouplingCounterPorts))

theorem preparedSharedLocalFeedCouplingInterval_exec (hQ : SS.states ≤ Q) {P q w s t u band a b origin N : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t)
    (C B : ZMod s → GaussianInt)
    (hfit : origin+N ≤ s)
    (tail pageTail rhsTail raw : List (Fin (A+4))) (v : HS 168 Q A U) (S : Stacks 168 A)
    (hready : CouplingReady P q w s t u band a b raw (embStk sharedCouplingCoreReg S))
    (hlocalOrigin : origin = a) (hlocalEnd : b = a+N) (hsep : N+band ≤ s)
    (hsource : S.R 132 = cstream A w (packedInterval a N C)++tail) (h127 : S.R 127 = [])
    (hrows : (S.R 140).length = 2*band+1)
    (hpage : S.R 138 = cstream A w (couplingCoefficientPageInterval P q s t u band a b origin N)++pageTail)
    (hrhs : S.R 93 = cstream A w (packedInterval origin N B)++rhsTail)
    (h143 : S.R 143 = [])
    (hCfits : ∀ j, Fits w (C j))
    (has : ∀ j < N, ∀ z ∈ couplingCoefficientWords P q s t u band (origin+j), Fits w z ∧ z.im = 0)
    (V : ℕ) (h166 : S.R 166 = [])
    (h139 : (S.R 139).length = (couplingCoefficientPageInterval P q s t u band a b origin N).length)
    (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (hwide : 8*(t+1)^2+4*band+8 < 2^V)
    (hfitV : origin+(N+2*band)+s < 2^V)
    (hgeometry : CouplingIntervalMetadata V s t band a b origin N S)
    (h158 : S.R 158 = []) (h135 : S.R 135 = []) (h167 : S.R 167 = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ preparedSharedLocalFeedCouplingIntervalCost boundary P q w s t u band a b origin N V ∧
      Exec body (preparedSharedLocalFeedCouplingInterval hQ boundary) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 93 rhsTail) 110
          (cstream A w (packedInterval origin N (guardedCouplingRowField P q t u band a b boundary C B))++S.R 110))}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁,hreadyK⟩ := sharedCouplingCounters_exec (body := body) hw5 hqw raw v S hready
  let K : Stacks 168 A := {S with R := sharedCouplingCountersR q w S.R}
  have hhigh (k : Fin 168) (hk : 97 ≤ k.val) : K.R k = S.R k := sharedCouplingCountersR_high q w S.R k hk
  have hgeometryK : CouplingIntervalMetadata V s t band a b origin N K := by
    constructor
    · simpa only [hhigh 163 (by decide)] using hgeometry.width
    · intro k hk
      have h97 : 97 ≤ k.val := by
        simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [hhigh k h97]
      exact hgeometry.encoded k hk
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := sharedLocalFeedCouplingInterval_exec (body := body)
    hQ boundary hA hw5 hqw hst C B hfit tail pageTail rhsTail raw v₁ K hreadyK hlocalOrigin hlocalEnd hsep
    (by rw [hhigh 132 (by decide)]; exact hsource)
    (by rw [hhigh 127 (by decide)]; exact h127)
    (by rw [hhigh 140 (by decide)]; exact hrows)
    (by rw [hhigh 138 (by decide)]; exact hpage)
    (by simpa only [K,sharedCouplingCountersR_rhs] using hrhs)
    (by rw [hhigh 143 (by decide)]; exact h143) hCfits has V
    (by rw [hhigh 166 (by decide)]; exact h166)
    (by rw [hhigh 139 (by decide)]; exact h139)
    haS hbS hbandS hwide hfitV hgeometryK
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
  refine ⟨v₃,m₁+(m₂+(2*(w+q+Schoenhage.Schedule.topN w)+7)),hu₃.trans (hu₂.trans hu₁),(by dsimp only [preparedSharedLocalFeedCouplingIntervalCost]; omega),
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast ?_ (congrArg (mk v₃) hfinal)⟩
  rw [hsum]
  simp [sharedCouplingCounterPorts]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
