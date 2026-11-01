module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedPreparedLocalRibbon
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedPackedCouplingInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseCouplingRibbon

/-! The retained local result supplies the masked ribbon, without an ambient
source tape. Retained spatial arithmetic and ribbon release are unchanged;
only RHS consumption and returned results survive. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {Q A : ℕ} {U : Type} {body : Empty → Pr Empty 168 Q A U}

noncomputable def cachedLocalCouplingInterval (hQ : SS.states ≤ Q) : Pr Empty 168 Q A U :=
  .seq (cachedPreparedLocalRibbon 159)
    (.seq (cachedGuardCouplingInterval hQ 161) releaseCouplingRibbon)

noncomputable def cachedLocalCouplingWorkspace (P K q w s t u band a b origin N V : ℕ) : ℕ :=
  mnProgPush (cachedPreparedLocalRibbon (P := Empty) (Q := Q) (A := A) (U := U) 159)*((16*N*w+21*N+14*band*w+13*band+11*V+46)+cachedGatheredRibbonCost (N+2*band) w+(12*((N+2*band)*w)+11*(N+2*band)+14))+((2*(6*N+6)+(3*(6*N+11*V+6)+((realWeightWorkspace K w (2*band+1)+13000*(band+1)*(w+1))+3*(22*N+22*V+22+transferCountedLineCost N w+transferCountedLineCost (couplingCoefficientPageInterval P q s t u band a b origin N).length w))))+mnProgPush (releaseCouplingRibbon (P := Empty) (Q := Q) (A := A) (U := U))*(12*((N+2*band)*w)+17*N+26*band+11*V+24))

theorem cachedLocalCouplingInterval_exec_within (hQ : SS.states ≤ Q) {P q w s t u band a b origin N : ℕ} [NeZero s]
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
    (hxs : ∀ j < N, ∀ x ∈ couplingInputWords boundary t band a b (origin+j) C, Fits w x)
    (has : ∀ j < N, ∀ z ∈ couplingCoefficientWords P q s t u band (origin+j), Fits w z ∧ z.im = 0)
    (V : ℕ) (hNV : N < 2^V) (h165 : S.R 165 = binSyms V N) (h166 : S.R 166 = [])
    (h139 : (S.R 139).length = (couplingCoefficientPageInterval P q s t u band a b origin N).length)
    (hbS : b ≤ s) (hbandS : band ≤ s)
    (h159 : S.R 159 = (couplingRibbonFlags (s := s) boundary t band a b origin N).map
      (fun flag => pairSym A flag flag))
    (h161 : S.R 161 = recoveryGuardIntervalSymbols true A s t (2*band) a b origin N)
    (h158 : S.R 158 = []) (h135 : S.R 135 = []) (h167 : S.R 167 = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ ((16*N*w+21*N+14*band*w+13*band+11*V+46)+cachedGatheredRibbonCost (N+2*band) w+(12*((N+2*band)*w)+11*(N+2*band)+14)) +
        (12*((N+2*band)*w)+17*N+26*band+11*V+24) +
        ((6*N+6)+(6*N+11*V+6+(retainedPageSpatialIntervalLoopCost boundary q w s t band a b origin N+
        (22*N+22*V+22+transferCountedLineCost N w+
          transferCountedLineCost (couplingCoefficientPageInterval P q s t u band a b origin N).length w)))) ∧
      ∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          cachedLocalCouplingWorkspace (Q := Q) (A := A) (U := U) P K q w s t u band a b origin N V)
        depth (cachedLocalCouplingInterval hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 93 rhsTail) 113
          (cstream A w (packedInterval origin N (guardedCouplingRowField P q t u band a b boundary C B)).reverse++S.R 113))}) := by
  have hsmall (i : Fin 3) : S.R ⟨i.val,by omega⟩ = [] := by
    have hh := hready.low ⟨i.val,by omega⟩ (by change i.val < 63; have := i.isLt; omega)
    exact hh
  have hfresh (k : Fin 117) (hk : k ∈ [(96 : Fin 117),102,104,105,106,108,109,115,116]) :
      S.R (intervalPageReg (groupReg k)) = [] := hready.fresh k hk
  have h104 : S.R 104 = [] := hfresh 104 (by simp)
  have h105 : S.R 105 = [] := hfresh 105 (by simp)
  have h108 : S.R 108 = [] := hfresh 108 (by simp)
  have h109 : S.R 109 = [] := hfresh 109 (by simp)
  have hband : (S.R 100).length = band := hready.bandwidth
  have hw : (S.R 94).length = w := hready.width
  have hclean : ∀ k ∈ ([(0 : Fin 168),1,2,104,105,108,109,127,158,166]), S.R k = [] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsmall 0
    · exact hsmall 1
    · exact hsmall 2
    · exact h104
    · exact h105
    · exact h108
    · exact h109
    · exact h127
    · exact h158
    · exact h166
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := cachedPreparedLocalRibbon_exec (body := body) boundary 159
    (by decide) (by decide) (by decide) (by decide) hst hbS hbandS hfit v S h159 hclean
    hlocalOrigin hlocalEnd hsep C w tail (by omega) hNV h165 hband hw hsource h135 h167 h143
  let G : Stacks 168 A := {S with R := (Function.update S.R 141
    (cstream A w (couplingSourceInterval boundary t band a b origin N C)++S.R 141))}
  have hreadyG : RetainedCouplingReady P q w s t u band a b raw
      (embStk groupReg (embStk intervalPageReg G)) := by
    rw [show embStk groupReg (embStk intervalPageReg G) = embStk groupReg (embStk intervalPageReg S)
      from intervalPageCore_updateR S 141 (by decide) _]
    exact hready
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := cachedPackedCouplingInterval_exec_within (body := body)
    hQ 161 (by decide) boundary hA hw5 hqw hst C B hfit (S.R 141) pageTail rhsTail raw K hpush v₁ G hreadyG
    (by simp [G]) (by simpa [G] using hrows) (by simpa [G] using hpage)
    (by simpa [G] using hrhs) (by simpa [G] using h143)
    hxs has V hNV (by simpa [G] using h165) (by simpa [G] using h166)
    (by simpa [G] using h139) (by simpa [G] using h161)
  let F : Stacks 168 A := {G with R := (Function.update (Function.update G.R 93 rhsTail) 113
    (cstream A w (packedInterval origin N (guardedCouplingRowField P q t u band a b boundary C B)).reverse++G.R 113))}
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := releaseCouplingRibbon_exec (body := body) V N band w hNV v₂ F
    (cstream A w (couplingSourceInterval boundary t band a b origin N C)) (S.R 141)
    (by simp [F,G]) (by rw [length_cstream,couplingSourceInterval_length _ _ _ _ _ _ _ _ hfit])
    (by simpa [F,G] using h165) (by simpa [F,G] using h166)
    (by simpa [F,G] using hband) (by simpa [F,G] using hw)
    (by simpa [F,G] using h109) (by simpa [F,G] using hsmall 0)
    (by simpa [F,G] using hsmall 1) (by simpa [F,G] using hsmall 2)
    (by simpa [F,G] using h108) (by simpa [F,G] using h167)
    (by simpa [F,G] using h104) (by simpa [F,G] using h105)
  refine ⟨v₃,m₁+(m₂+m₃),hu₃.trans (hu₂.trans hu₁),by omega,?_⟩
  intro depth
  have ht₁ := mn_native_exec_within he₁ (mnProgPush (cachedPreparedLocalRibbon (P := Empty) (Q := Q) (A := A) (U := U) 159)) (WordCmd.empty_native _) depth
    (mnSize (mk v S)+depth+mnProgPush (cachedPreparedLocalRibbon (P := Empty) (Q := Q) (A := A) (U := U) 159)*((16*N*w+21*N+14*band*w+13*band+11*V+46)+cachedGatheredRibbonCost (N+2*band) w+(12*((N+2*band)*w)+11*(N+2*band)+14)))
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ hm₁) _)
  have ht₃ := mn_native_exec_within he₃ (mnProgPush (releaseCouplingRibbon (P := Empty) (Q := Q) (A := A) (U := U))) (WordCmd.empty_native _) depth
    (mnSize (mk v₂ F)+depth+mnProgPush (releaseCouplingRibbon (P := Empty) (Q := Q) (A := A) (U := U))*(12*((N+2*band)*w)+17*N+26*band+11*V+24))
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ hm₃) _)
  have ht₂ := mn_seq_within_add (a := (2*(6*N+6)+(3*(6*N+11*V+6)+((realWeightWorkspace K w (2*band+1)+13000*(band+1)*(w+1))+3*(22*N+22*V+22+transferCountedLineCost N w+transferCountedLineCost (couplingCoefficientPageInterval P q s t u band a b origin N).length w))))) (b := mnProgPush (releaseCouplingRibbon (P := Empty) (Q := Q) (A := A) (U := U))*(12*((N+2*band)*w)+17*N+26*band+11*V+24)) (he₂ depth) ht₃
  refine (mn_seq_within_add (a := mnProgPush (cachedPreparedLocalRibbon (P := Empty) (Q := Q) (A := A) (U := U) 159)*((16*N*w+21*N+14*band*w+13*band+11*V+46)+cachedGatheredRibbonCost (N+2*band) w+(12*((N+2*band)*w)+11*(N+2*band)+14))) (b := (2*(6*N+6)+(3*(6*N+11*V+6)+((realWeightWorkspace K w (2*band+1)+13000*(band+1)*(w+1))+3*(22*N+22*V+22+transferCountedLineCost N w+transferCountedLineCost (couplingCoefficientPageInterval P q s t u band a b origin N).length w))))+mnProgPush (releaseCouplingRibbon (P := Empty) (Q := Q) (A := A) (U := U))*(12*((N+2*band)*w)+17*N+26*band+11*V+24)) ht₁ ht₂).cast rfl ?_
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext r
  by_cases h1 : r = 141 <;> by_cases h2 : r = 93 <;> by_cases h3 : r = 113 <;>
    simp [F,G,h1,h2,h3]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
