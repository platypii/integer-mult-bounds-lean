module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBuildPreparedLocalRibbon
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedRestoredPackedCouplingInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseCouplingRibbon

/-! The retained local result supplies the masked ribbon, without an ambient
source tape. Retained spatial arithmetic and ribbon release are unchanged;
only RHS consumption and returned results survive. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 168 Q A U}

noncomputable def localCouplingInterval (hQ : SS.states ≤ Q) (boundary : Bool) : Pr P₀ 168 Q A U :=
  .seq (buildPreparedLocalRibbon boundary)
    (.seq (generatedRestoredCouplingInterval hQ boundary) releaseCouplingRibbon)

theorem localCouplingInterval_exec (hQ : SS.states ≤ Q) {P q w s t u band a b origin N : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t)
    (C B : ZMod s → GaussianInt)
    (hfit : origin+N ≤ s)
    (tail pageTail rhsTail raw : List (Fin (A+4))) (v : HS 168 Q A U) (S : Stacks 168 A)
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
    (value : Fin 117 → ℕ) (hvs : value 97 = s) (hvt : value 98 = t)
    (hvb : value 100 = 2*band) (hva : value 101 = a) (hvu : value 103 = b)
    (hvi : value 107 = origin) (hvc : value 108 = origin+N)
    (haS : a ≤ s) (hbS : b ≤ s) (hwide : 8*(t+1)^2+4*band+8 < 2^V)
    (hbound : ∀ i, value (intervalGuardBankSource i) < 2^V)
    (hV : ((embStk intervalGuardPlacement S).R 115).length = V)
    (hmeta : ∀ i, (embStk intervalGuardPlacement S).R (intervalGuardBankSource i) =
      binSyms V (value (intervalGuardBankSource i)))
    (ribbonValue : Fin 168 → ℕ)
    (hrs : ribbonValue 145 = s) (hrt : ribbonValue 146 = t) (hrband : ribbonValue 147 = band)
    (hra : ribbonValue 149 = a) (hrb : ribbonValue 151 = b) (hri : ribbonValue 155 = origin)
    (hrc : ribbonValue 164 = origin+(N+2*band)) (hbandS : band ≤ s)
    (hfitV : origin+(N+2*band)+s < 2^V)
    (hrbound : ∀ i, ribbonValue (ribbonMaskBankSource i) < 2^V)
    (hrV : (S.R 163).length = V)
    (hrmeta : ∀ i, S.R (ribbonMaskBankSource i) = binSyms V (ribbonValue (ribbonMaskBankSource i)))
    (h158 : S.R 158 = []) (h135 : S.R 135 = []) (h167 : S.R 167 = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ ((16*N*w+21*N+14*band*w+13*band+11*V+46)+(152*V+153+((32*(N+2*band)+2)*tblC V 1+68*V+2*(N+2*band)+72)+maskCouplingSourceCost (N+2*band) w)+(12*((N+2*band)*w)+11*(N+2*band)+14)) +
        (12*((N+2*band)*w)+17*N+26*band+11*V+24) +
        (144*V+145+((46*N+2)*tblC V 1+66*V+2*N+70)+(6*N+11*V+6+(retainedPageSpatialIntervalLoopCost boundary q w s t band a b origin N+
        (22*N+22*V+22+transferCountedLineCost N w+
          transferCountedLineCost (couplingCoefficientPageInterval P q s t u band a b origin N).length w)))) ∧
      Exec body (localCouplingInterval hQ boundary) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 93 rhsTail) 113
          (cstream A w (packedInterval origin N (guardedCouplingRowField P q t u band a b boundary C B)).reverse++S.R 113))}) := by
  have hblank : ∀ r, S.R (ribbonTableReg r) = [] := by
    intro r
    have hr := ribbonTableReg_range r
    have hk : (⟨(ribbonTableReg r).val,by omega⟩ : Fin 117).val < 63 := hr.trans (by decide)
    exact hready.low ⟨(ribbonTableReg r).val,by omega⟩ hk
  have hsmall (i : Fin 18) : S.R (ribbonTableReg (.v i)) = [] := hblank (.v i)
  have hfresh (k : Fin 117) (hk : k ∈ [(96 : Fin 117),102,104,105,106,108,109,115,116]) :
      S.R (intervalPageReg (groupReg k)) = [] := hready.fresh k hk
  have h104 : S.R 104 = [] := hfresh 104 (by simp)
  have h105 : S.R 105 = [] := hfresh 105 (by simp)
  have h108 : S.R 108 = [] := hfresh 108 (by simp)
  have h109 : S.R 109 = [] := hfresh 109 (by simp)
  have hband : (S.R 100).length = band := hready.bandwidth
  have hw : (S.R 94).length = w := hready.width
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := buildPreparedLocalRibbon_exec (body := body) boundary ribbonValue
    hrs hrt hrband hra hrb hri hrc hst haS hbS hbandS hfit hfitV (by omega) hrbound v S
    hrV hrmeta hblank hlocalOrigin hlocalEnd hsep C w tail (by omega) h165 h166 h127 h109 hband hw hsource
    h158 h108 h104 h105 h135 h167 h143
  let G : Stacks 168 A := {S with R := (Function.update S.R 141
    (cstream A w (couplingSourceInterval boundary t band a b origin N C)++S.R 141))}
  have hreadyG : RetainedCouplingReady P q w s t u band a b raw
      (embStk groupReg (embStk intervalPageReg G)) := by
    rw [show embStk groupReg (embStk intervalPageReg G) = embStk groupReg (embStk intervalPageReg S)
      from intervalPageCore_updateR S 141 (by decide) _]
    exact hready
  have hmetaG : ∀ i, (embStk intervalGuardPlacement G).R (intervalGuardBankSource i) =
      binSyms V (value (intervalGuardBankSource i)) := by
    intro i
    have hn : intervalGuardPlacement (intervalGuardBankSource i) ≠ 141 := by
      simp only [intervalGuardBankSource]; split_ifs <;> decide
    simpa only [G,embStk,Function.comp_def,Function.update_of_ne hn] using hmeta i
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := generatedRestoredPackedCouplingInterval_exec (body := body)
    hQ boundary hA hw5 hqw hst C B hfit (S.R 141) pageTail rhsTail raw v₁ G hreadyG
    (by simp [G]) (by simpa [G] using hrows) (by simpa [G] using hpage)
    (by simpa [G] using hrhs) (by simpa [G] using h143)
    hxs has V hNV (by simpa [G] using h165) (by simpa [G] using h166)
    (by simpa [G] using h139) value hvs hvt hvb hva hvu hvi hvc haS hbS hwide hbound
    (by simpa [G,embStk,intervalGuardPlacement] using hV) hmetaG
  let F : Stacks 168 A := {G with R := (Function.update (Function.update G.R 93 rhsTail) 113
    (cstream A w (packedInterval origin N (guardedCouplingRowField P q t u band a b boundary C B)).reverse++G.R 113))}
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := releaseCouplingRibbon_exec (body := body) V N band w hNV v₂ F
    (cstream A w (couplingSourceInterval boundary t band a b origin N C)) (S.R 141)
    (by simp [F,G]) (by rw [length_cstream,couplingSourceInterval_length _ _ _ _ _ _ _ _ hfit])
    (by simpa [F,G] using h165) (by simpa [F,G] using h166)
    (by simpa [F,G] using hband) (by simpa [F,G] using hw)
    (by simpa [F,G] using h109) (by simpa [F,G,ribbonTableReg] using hsmall 0)
    (by simpa [F,G,ribbonTableReg] using hsmall 1) (by simpa [F,G,ribbonTableReg] using hsmall 2)
    (by simpa [F,G] using h108) (by simpa [F,G] using h167)
    (by simpa [F,G] using h104) (by simpa [F,G] using h105)
  refine ⟨v₃,m₁+(m₂+m₃),hu₃.trans (hu₂.trans hu₁),by omega,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext r
  by_cases h1 : r = 141 <;> by_cases h2 : r = 93 <;> by_cases h3 : r = 113 <;>
    simp [F,G,h1,h2,h3]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
