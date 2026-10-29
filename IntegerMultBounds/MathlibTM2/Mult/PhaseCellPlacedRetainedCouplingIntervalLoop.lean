module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedPageSpatialCouplingRowLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedFinishCouplingCoefficientInterval

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 168 Q A U}

noncomputable def placedRetainedCouplingIntervalLoop (hQ : SS.states ≤ Q) : Pr P₀ 168 Q A U :=
  embProg intervalPageReg Empty.elim (retainedPageSpatialCouplingRowLoop (P₀ := Empty) hQ)

theorem placedRetainedCouplingIntervalLoop_exec (hQ : SS.states ≤ Q) {P q w s t u band a b origin : ℕ} [NeZero s]
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
    (has : ∀ j < rhs.length, ∀ z ∈ couplingCoefficientWords P q s t u band (origin+j), Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧ m ≤ retainedPageSpatialIntervalLoopCost boundary q w s t band a b origin rhs.length ∧
      Exec (body) (placedRetainedCouplingIntervalLoop hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update S.R 136 maskTail) 138 pageTail) 137
          ((cstream A w (couplingCoefficientPageInterval P q s t u band a b origin rhs.length)).reverse++S.R 137))
          93 rhsTail) 107 (List.replicate rhs.length tick++S.R 107))
          113 (cstream A w (guardedCouplingRowWords P q t u band a b boundary C origin rhs).reverse++S.R 113)) 143 [])
          141 (cstream A w (source.drop rhs.length)++tail))
          142 ((cstream A w (source.take rhs.length)).reverse++S.R 142))}) := by
  obtain ⟨v₁,m,hu₁,hm,he⟩ := retainedPageSpatialCouplingRowLoop_interval_exec
    (body := fun p : Empty => nomatch p) hQ boundary hA hw5 hqw hst C source rhs hlen hwindow hfit
    tail pageTail maskTail rhsTail raw (embDn intervalPageReg v) (embStk intervalPageReg S)
    hready hsource hrows hpage hmask hrhs hcount hxs has
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    intervalPageReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v₂,m,hu₂.trans hu₁,hm,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  let T := embStk intervalPageReg S
  let T1 : Stacks 144 A := {T with R := (Function.update T.R 136 (maskTail))}
  let T2 : Stacks 144 A := {T1 with R := (Function.update T1.R 138 (pageTail))}
  let T3 : Stacks 144 A := {T2 with R := (Function.update T2.R 137 ((cstream A w (couplingCoefficientPageInterval P q s t u band a b origin rhs.length)).reverse++T.R 137))}
  let T4 : Stacks 144 A := {T3 with R := (Function.update T3.R 93 (rhsTail))}
  let T5 : Stacks 144 A := {T4 with R := (Function.update T4.R 107 (List.replicate rhs.length tick++T.R 107))}
  let T6 : Stacks 144 A := {T5 with R := (Function.update T5.R 113 (cstream A w (guardedCouplingRowWords P q t u band a b boundary C origin rhs).reverse++T.R 113))}
  let T7 : Stacks 144 A := {T6 with R := (Function.update T6.R 143 ([]))}
  let T8 : Stacks 144 A := {T7 with R := (Function.update T7.R 141 (cstream A w (source.drop rhs.length)++tail))}
  change embOvr intervalPageReg ({T8 with R := (Function.update T8.R 142 ((cstream A w (source.take rhs.length)).reverse++T.R 142))} : Stacks 144 A).get S = _
  rw [embOvr_updR intervalPageReg_injective T8 S 142,
    embOvr_updR intervalPageReg_injective T7 S 141,
    embOvr_updR intervalPageReg_injective T6 S 143,
    embOvr_updR intervalPageReg_injective T5 S 113,
    embOvr_updR intervalPageReg_injective T4 S 107,
    embOvr_updR intervalPageReg_injective T3 S 93,
    embOvr_updR intervalPageReg_injective T2 S 137,
    embOvr_updR intervalPageReg_injective T1 S 138,
    embOvr_updR intervalPageReg_injective T S 136,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
