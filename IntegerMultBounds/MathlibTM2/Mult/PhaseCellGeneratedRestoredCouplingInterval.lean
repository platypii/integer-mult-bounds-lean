module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedRestoredCouplingInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedBinaryRecoveryGuardInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoreIntervalCouplingPass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedFinishCouplingCoefficientInterval

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 168 Q A U}

noncomputable def generatedRestoredCouplingInterval (hQ : SS.states ≤ Q) (boundary : Bool) : Pr P₀ 168 Q A U :=
  .seq (placedBinaryRecoveryGuardInterval true) (countedRestoredCouplingInterval hQ)

theorem generatedRestoredCouplingInterval_exec (hQ : SS.states ≤ Q) {P q w s t u band a b origin : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t)
    (C : ZMod s → GaussianInt) (source rhs : List GaussianInt)
    (hlen : rhs.length ≤ source.length)
    (hwindow : ∀ j < rhs.length, (source.drop j).take (2*band+1) = spatialCouplingInputWords boundary t band a b (origin+j) C) (hfit : origin+rhs.length ≤ s)
    (tail pageTail rhsTail raw : List (Fin (A+4))) (v : HS 168 Q A U) (S : Stacks 168 A)
    (hready : RetainedCouplingReady P q w s t u band a b raw (embStk groupReg (embStk intervalPageReg S)))
    (hsource : S.R 141 = cstream A w source++tail)
    (hrows : (S.R 140).length = 2*band+1)
    (hpage : S.R 138 = cstream A w (couplingCoefficientPageInterval P q s t u band a b origin rhs.length)++pageTail)
    (hrhs : S.R 93 = cstream A w rhs++rhsTail)
    (h143 : S.R 143 = [])
    (hxs : ∀ j < rhs.length, ∀ x ∈ couplingInputWords boundary t band a b (origin+j) C, Fits w x)
    (has : ∀ j < rhs.length, ∀ z ∈ couplingCoefficientWords P q s t u band (origin+j), Fits w z ∧ z.im = 0)
    (V : ℕ) (hNV : rhs.length < 2^V) (h165 : S.R 165 = binSyms V rhs.length) (h166 : S.R 166 = [])
    (h139 : (S.R 139).length = (couplingCoefficientPageInterval P q s t u band a b origin rhs.length).length)
    (value : Fin 117 → ℕ) (hvs : value 97 = s) (hvt : value 98 = t)
    (hvb : value 100 = 2*band) (hva : value 101 = a) (hvu : value 103 = b)
    (hvi : value 107 = origin) (hvc : value 108 = origin+rhs.length)
    (haS : a ≤ s) (hbS : b ≤ s) (hwide : 8*(t+1)^2+4*band+8 < 2^V)
    (hbound : ∀ i, value (intervalGuardBankSource i) < 2^V)
    (hV : ((embStk intervalGuardPlacement S).R 115).length = V)
    (hmeta : ∀ i, (embStk intervalGuardPlacement S).R (intervalGuardBankSource i) =
      binSyms V (value (intervalGuardBankSource i))) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ 144*V+145+((46*rhs.length+2)*tblC V 1+66*V+2*rhs.length+70)+(6*rhs.length+11*V+6+(retainedPageSpatialIntervalLoopCost boundary q w s t band a b origin rhs.length+
        (22*rhs.length+22*V+22+transferCountedLineCost rhs.length w+
          transferCountedLineCost (couplingCoefficientPageInterval P q s t u band a b origin rhs.length).length w))) ∧
      Exec body (generatedRestoredCouplingInterval hQ boundary) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 93 rhsTail) 113
          (cstream A w (guardedCouplingRowWords P q t u band a b boundary C origin rhs).reverse++S.R 113))}) := by
  have hblank : ∀ r, (embStk intervalGuardPlacement S).R (intervalGuardReg r) = [] := by
    intro r
    have hr := intervalGuardReg_range r
    let k : Fin 117 := intervalGuardReg r
    have hne : k ≠ 109 := by intro he; have hv := congrArg (fun j : Fin 117 => j.val) he; dsimp [k] at hv; norm_num at hv; omega
    have hh := hready.low k (by dsimp [k]; omega)
    change S.R (intervalGuardPlacement k) = []
    simp only [intervalGuardPlacement,if_neg hne,if_pos (show k.val < 96 by dsimp [k]; omega)]
    exact hh
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := placedBinaryRecoveryGuardInterval_exec (body := body) true value
    hvs hvt hvb hva hvu hvi hvc hfit (NeZero.pos s) hst haS hbS (by omega) hbound v S hV hmeta hblank
  let G : Stacks 168 A := {S with R := (Function.update S.R 136
    (recoveryGuardIntervalSymbols true A s t (2*band) a b origin rhs.length++S.R 136))}
  have hreadyG : RetainedCouplingReady P q w s t u band a b raw
      (embStk groupReg (embStk intervalPageReg G)) := by
    rw [show embStk groupReg (embStk intervalPageReg G) = embStk groupReg (embStk intervalPageReg S)
      from intervalPageCore_updateR S 136 (by decide) _]
    exact hready
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := countedRestoredCouplingInterval_exec (body := body)
    hQ boundary hA hw5 hqw hst C source rhs hlen hwindow hfit tail pageTail (S.R 136) rhsTail raw v₁ G hreadyG
    (by simpa [G] using hsource) (by simpa [G] using hrows) (by simpa [G] using hpage)
    (by change recoveryGuardIntervalSymbols true A s t (2*band) a b origin rhs.length++S.R 136 = _
        rw [recoveryGuardIntervalSymbols_coupling _ _ _ _ _ _ _ _ hfit]; rfl)
    (by simpa [G] using hrhs) (by simpa [G] using h143)
    hxs has V hNV (by simpa [G] using h165) (by simpa [G] using h166) (by simpa [G] using h139)
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,by omega,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext r
  by_cases h1 : r = 136 <;> by_cases h2 : r = 93 <;> by_cases h3 : r = 113 <;>
    by_cases h4 : r = 143 <;> simp [G,h1,h2,h3,h4,h143]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
