module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoredRetainedCouplingInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoreIntervalCouplingPass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedFinishCouplingCoefficientInterval

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 168 Q A U}

noncomputable def countedRestoredCouplingInterval (hQ : SS.states ≤ Q) : Pr P₀ 168 Q A U :=
  .seq (toUnary 165 143 0 1 2) (restoredRetainedCouplingInterval hQ)

theorem countedRestoredCouplingInterval_exec (hQ : SS.states ≤ Q) {P q w s t u band a b origin : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t)
    (C : ZMod s → GaussianInt) (source rhs : List GaussianInt)
    (hlen : rhs.length ≤ source.length)
    (hwindow : ∀ j < rhs.length, (source.drop j).take (2*band+1) = spatialCouplingInputWords boundary t band a b (origin+j) C) (hfit : origin+rhs.length ≤ s)
    (tail pageTail maskTail rhsTail raw : List (Fin (A+4))) (v : HS 168 Q A U) (S : Stacks 168 A)
    (hready : RetainedCouplingReady P q w s t u band a b raw (embStk groupReg (embStk intervalPageReg S)))
    (hsource : S.R 141 = cstream A w source++tail)
    (hrows : (S.R 140).length = 2*band+1)
    (hpage : S.R 138 = cstream A w (couplingCoefficientPageInterval P q s t u band a b origin rhs.length)++pageTail)
    (hmask : S.R 136 = ((couplingGuardSymbols boundary A s t band a b).drop origin).take rhs.length++maskTail)
    (hrhs : S.R 93 = cstream A w rhs++rhsTail)
    (h143 : S.R 143 = [])
    (hxs : ∀ j < rhs.length, ∀ x ∈ couplingInputWords boundary t band a b (origin+j) C, Fits w x)
    (has : ∀ j < rhs.length, ∀ z ∈ couplingCoefficientWords P q s t u band (origin+j), Fits w z ∧ z.im = 0)
    (V : ℕ) (hNV : rhs.length < 2^V) (h165 : S.R 165 = binSyms V rhs.length) (h166 : S.R 166 = [])
    (h139 : (S.R 139).length = (couplingCoefficientPageInterval P q s t u band a b origin rhs.length).length) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ 6*rhs.length+11*V+6+(retainedPageSpatialIntervalLoopCost boundary q w s t band a b origin rhs.length+
        (22*rhs.length+22*V+22+transferCountedLineCost rhs.length w+
          transferCountedLineCost (couplingCoefficientPageInterval P q s t u band a b origin rhs.length).length w)) ∧
      Exec body (countedRestoredCouplingInterval hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          136 maskTail) 93 rhsTail) 113
          (cstream A w (guardedCouplingRowWords P q t u band a b boundary C origin rhs).reverse++S.R 113)) 143 [])}) := by
  have hsmall (r : Fin 168) (hr : r.val < 3) : S.R r = [] := by
    let k : Fin 117 := ⟨r.val,by omega⟩
    have hk := hready.low k (by dsimp [k]; omega)
    simpa [embStk,groupReg,intervalPageReg,k] using hk
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := toUnary_exec_linear (body := body)
    (a := 165) (z := 143) (w := 0) (t := 1) (t₂ := 2) (by decide) hNV v S h165
    (hsmall 0 (by decide)) (hsmall 1 (by decide)) (hsmall 2 (by decide))
  let B : Stacks 168 A := {S with R := Function.update S.R 143 (List.replicate rhs.length tick)}
  have he₁' : Exec body (toUnary 165 143 0 1 2) (mk v S) n₁ (mk v₁ B) := by
    simpa only [h143,List.append_nil] using he₁
  have hreadyB : RetainedCouplingReady P q w s t u band a b raw
      (embStk groupReg (embStk intervalPageReg B)) := by
    rw [show embStk groupReg (embStk intervalPageReg B) = embStk groupReg (embStk intervalPageReg S)
      from intervalPageCore_updateR S 143 (by decide) _]
    exact hready
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := restoredRetainedCouplingInterval_exec (body := body)
    hQ boundary hA hw5 hqw hst C source rhs hlen hwindow hfit
    tail pageTail maskTail rhsTail raw v₁ B hreadyB
    (by simpa [B] using hsource) (by simpa [B] using hrows) (by simpa [B] using hpage)
    (by simpa [B] using hmask) (by simpa [B] using hrhs)
    (by simp [B]) hxs has V hNV (by simpa [B] using h165) (by simpa [B] using h166)
    (by simpa [B] using h139)
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,by omega,(Exec.seq he₁' he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext r
  by_cases h1 : r = 143 <;> by_cases h2 : r = 136 <;> by_cases h3 : r = 93 <;>
    by_cases h4 : r = 113 <;> simp [B,h1,h2,h3,h4]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
