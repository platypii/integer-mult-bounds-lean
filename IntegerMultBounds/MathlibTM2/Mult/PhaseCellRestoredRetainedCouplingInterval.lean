module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedRetainedCouplingIntervalLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoreIntervalCouplingPass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedFinishCouplingCoefficientInterval

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 168 Q A U}

noncomputable def restoredRetainedCouplingInterval (hQ : SS.states ≤ Q) : Pr P₀ 168 Q A U :=
  .seq (placedRetainedCouplingIntervalLoop hQ) restoreIntervalCouplingPass

theorem restoredRetainedCouplingInterval_exec (hQ : SS.states ≤ Q) {P q w s t u band a b origin : ℕ} [NeZero s]
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
    (hcount : (S.R 143).length = rhs.length)
    (hxs : ∀ j < rhs.length, ∀ x ∈ couplingInputWords boundary t band a b (origin+j) C, Fits w x)
    (has : ∀ j < rhs.length, ∀ z ∈ couplingCoefficientWords P q s t u band (origin+j), Fits w z ∧ z.im = 0)
    (V : ℕ) (hNV : rhs.length < 2^V) (h165 : S.R 165 = binSyms V rhs.length) (h166 : S.R 166 = [])
    (h139 : (S.R 139).length = (couplingCoefficientPageInterval P q s t u band a b origin rhs.length).length) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ retainedPageSpatialIntervalLoopCost boundary q w s t band a b origin rhs.length+
        (22*rhs.length+22*V+22+transferCountedLineCost rhs.length w+
          transferCountedLineCost (couplingCoefficientPageInterval P q s t u band a b origin rhs.length).length w) ∧
      Exec body (restoredRetainedCouplingInterval hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          136 maskTail) 93 rhsTail) 113
          (cstream A w (guardedCouplingRowWords P q t u band a b boundary C origin rhs).reverse++S.R 113)) 143 [])}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := placedRetainedCouplingIntervalLoop_exec (body := body) hQ
    boundary hA hw5 hqw hst C source rhs hlen hwindow hfit tail pageTail maskTail rhsTail raw v S
    hready hsource hrows hpage hmask hrhs hcount hxs has
  let F : Stacks 168 A := {S with R := (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update S.R 136 maskTail) 138 pageTail) 137
          ((cstream A w (couplingCoefficientPageInterval P q s t u band a b origin rhs.length)).reverse++S.R 137))
          93 rhsTail) 107 (List.replicate rhs.length tick++S.R 107))
          113 (cstream A w (guardedCouplingRowWords P q t u band a b boundary C origin rhs).reverse++S.R 113)) 143 [])
          141 (cstream A w (source.drop rhs.length)++tail))
          142 ((cstream A w (source.take rhs.length)).reverse++S.R 142))}
  have hsmall (r : Fin 168) (hr : r.val < 3) : S.R r = [] := by
    let k : Fin 117 := ⟨r.val,by omega⟩
    have hk := hready.low k (by dsimp [k]; omega)
    simpa [embStk,groupReg,intervalPageReg,k] using hk
  have h109 : S.R 109 = [] := hready.fresh 109 (by simp)
  have h104 : S.R 104 = [] := hready.fresh 104 (by simp)
  have h105 : S.R 105 = [] := hready.fresh 105 (by simp)
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := restoreIntervalCouplingPass_exec (body := body)
    V rhs.length w hNV source hlen tail (S.R 142) (S.R 107)
    (couplingCoefficientPageInterval P q s t u band a b origin rhs.length) (S.R 137) v₁ F
    (by simpa [F] using h165) (by simpa [F] using h166)
    (by simpa [F,embStk,groupReg,intervalPageReg] using hready.width) (by simp [F]) (by simp [F]) (by simp [F])
    (by simpa [F] using hsmall 0 (by decide)) (by simpa [F] using hsmall 1 (by decide))
    (by simpa [F] using hsmall 2 (by decide)) (by simpa [F] using h139) (by simp [F])
    (by simpa [F] using h109) (by simpa [F] using h104) (by simpa [F] using h105)
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext r
  by_cases h93 : r = 93
  · subst r; simp [F]
  by_cases h107 : r = 107
  · subst r; simp [F]
  by_cases h113 : r = 113
  · subst r; simp [F]
  by_cases h136 : r = 136
  · subst r; simp [F]
  by_cases h137 : r = 137
  · subst r; simp [F]
  by_cases h138 : r = 138
  · subst r; simp [F,hpage]
  by_cases h141 : r = 141
  · subst r; simp [F,hsource]
  by_cases h142 : r = 142
  · subst r; simp [F]
  by_cases h143 : r = 143
  · subst r; simp [F]
  simp [F,h93,h107,h113,h136,h137,h138,h141,h142,h143]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
