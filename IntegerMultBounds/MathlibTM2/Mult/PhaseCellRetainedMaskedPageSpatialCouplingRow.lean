module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCouplingCoefficientPageCursor

/-! Read one active page row or copy an unobserved RHS, consuming one actual guard symbol. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

noncomputable def retainedGuardedPageSpatialCouplingRow (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  .cond (·.flag) (copyPrefix 94 93 113 104 105) (retainedConsumePageSpatialCouplingRow hQ)

def retainedGuardedPageSpatialCouplingRowCost (skip : Bool) (_q w band : ℕ) : ℕ :=
  (if skip then 10*w+10 else retainedConsumePageSpatialCouplingRowCost w band)+1

theorem retainedGuardedPageSpatialCouplingRow_prefix_exec (hQ : SS.states ≤ Q) {P q w s t u band a b i : ℕ} [NeZero s]
    (boundary skip : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (hi : i < s)
    (C : ZMod s → GaussianInt) (tail pageTail raw : List (Fin (A+4)))
    (v : HS 144 Q A U) (S : Stacks 144 A) (hflag : v.flag = skip)
    (hskip : skip = couplingSkipAt boundary s t band a b i)
    (hready : RetainedCouplingReady P q w s t u band a b raw (embStk groupReg S))
    (hrows : (S.R 140).length = 2*band+1)
    (hpage : S.R 138 = cstream A w (if skip then [] else spatialCouplingCoefficientWords P q s t u band i)++pageTail)
    (hsrc : S.R 141 = cstream A w (spatialCouplingInputWords boundary t band a b i C)++tail)
    (rhs : GaussianInt) (rhsTail : List (Fin (A+4))) (hrhs : S.R 93 = csyms A w rhs++rhsTail)
    (hxs : ∀ x ∈ couplingInputWords boundary t band a b i C, Fits w x)
    (has : ∀ z ∈ couplingCoefficientWords P q s t u band i, Fits w z ∧ z.im = 0) :
    let xs := if skip then [] else spatialCouplingCoefficientWords P q s t u band i
    ∃ v' m, v'.user = v.user ∧ m ≤ retainedGuardedPageSpatialCouplingRowCost skip q w band ∧
      Exec body (retainedGuardedPageSpatialCouplingRow hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 113
          (csyms A w (guardedCouplingRowWord P q t u band a b i boundary C rhs)++S.R 113))
          138 pageTail) 137 ((cstream A w xs).reverse++S.R 137))}) := by
  dsimp only
  cases skip with
  | true =>
    obtain ⟨v',hu,he⟩ := copyPrefix_exec (body := body) (count := 94) (src := 93) (dst := 113)
      (saved := 104) (tmp := 105) (by decide) v S (csyms A w rhs) rhsTail hrhs
      (by simpa [embStk,groupReg] using hready.width) (hready.fresh 104 (by simp)) (hready.fresh 105 (by simp))
    refine ⟨v',10*w+11,hu,by simp [retainedGuardedPageSpatialCouplingRowCost],?_⟩
    simp only [guardedCouplingRowWord,← hskip,ite_true,cstream_nil,List.reverse_nil,List.nil_append]
    have he' := Exec.cond_true (q := retainedConsumePageSpatialCouplingRow hQ) hflag he
    refine he'.cast (by simp) ?_
    apply congrArg (mk v')
    refine Stacks.ext rfl rfl rfl ?_
    have hp : S.R 138 = pageTail := by simpa using hpage
    funext k
    by_cases h113 : k = 113 <;> by_cases h138 : k = 138 <;> by_cases h137 : k = 137 <;> simp_all
  | false =>
    obtain ⟨v',m,hu,hm,he⟩ := retainedConsumePageSpatialCouplingRow_prefix_exec (body := body)
      hQ boundary hA hw5 hqw hst hi C tail pageTail raw v S hready hrows (by simpa using hpage) hsrc
      rhs rhsTail hrhs hxs has
    refine ⟨v',m+1,hu,by simpa [retainedGuardedPageSpatialCouplingRowCost] using Nat.add_le_add_right hm 1,?_⟩
    simp only [guardedCouplingRowWord,← hskip,Bool.false_eq_true,ite_false]
    exact Exec.cond_false hflag he

theorem retainedGuardedPageSpatialCouplingRow_exec (hQ : SS.states ≤ Q) {P q w s t u band a b i : ℕ} [NeZero s]
    (boundary skip : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (hi : i < s)
    (C : ZMod s → GaussianInt) (tail pageTail raw : List (Fin (A+4)))
    (v : HS 144 Q A U) (S : Stacks 144 A) (hflag : v.flag = skip)
    (hskip : skip = couplingSkipAt boundary s t band a b i)
    (hready : RetainedCouplingReady P q w s t u band a b raw (embStk groupReg S))
    (hrows : (S.R 140).length = 2*band+1)
    (hpage : S.R 138 = cstream A w (if skip then [] else spatialCouplingCoefficientWords P q s t u band i)++pageTail)
    (hsrc : S.R 141 = cstream A w ((cyclicPaddedLine (fun j : ZMod s =>
      if j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
      then C j else 0) band).drop i)++tail)
    (rhs : GaussianInt) (rhsTail : List (Fin (A+4))) (hrhs : S.R 93 = csyms A w rhs++rhsTail)
    (hxs : ∀ x ∈ couplingInputWords boundary t band a b i C, Fits w x)
    (has : ∀ z ∈ couplingCoefficientWords P q s t u band i, Fits w z ∧ z.im = 0) :
    let xs := if skip then [] else spatialCouplingCoefficientWords P q s t u band i
    ∃ v' m, v'.user = v.user ∧ m ≤ retainedGuardedPageSpatialCouplingRowCost skip q w band ∧
      Exec body (retainedGuardedPageSpatialCouplingRow hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 113
          (csyms A w (guardedCouplingRowWord P q t u band a b i boundary C rhs)++S.R 113))
          138 pageTail) 137 ((cstream A w xs).reverse++S.R 137))}) := by
  let F := fun j : ZMod s => if j ∈
    (if boundary then haloBoundary s t band a b else haloInterior s t band a b) then C j else 0
  let source := cyclicPaddedLine F band
  let rest := cstream A w ((source.drop i).drop (2*band+1))++tail
  have hwindow : spatialCouplingInputWords boundary t band a b i C = (source.drop i).take (2*band+1) :=
    spatialCouplingInputWords_window boundary t band a b i C hi
  have hp : S.R 141 = cstream A w (spatialCouplingInputWords boundary t band a b i C)++rest := by
    rw [hsrc,hwindow]
    dsimp only [rest,source,F]
    rw [← List.append_assoc,← cstream_append,List.take_append_drop]
  exact retainedGuardedPageSpatialCouplingRow_prefix_exec (body := body)
    hQ boundary skip hA hw5 hqw hst hi C rest pageTail raw v S hflag hskip hready hrows hpage hp rhs rhsTail hrhs hxs has

noncomputable def retainedMaskedPageSpatialCouplingRow (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  .seq (.act (.pop (.rt 136) (fun v o => {v with flag := pairRe (o.getD blank)}) .done))
    (retainedGuardedPageSpatialCouplingRow hQ)

theorem retainedMaskedPageSpatialCouplingRow_prefix_exec (hQ : SS.states ≤ Q) {P q w s t u band a b i : ℕ} [NeZero s]
    (boundary skip : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (hi : i < s)
    (C : ZMod s → GaussianInt) (tail pageTail raw : List (Fin (A+4)))
    (maskTail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hmask : S.R 136 = pairSym A skip skip::maskTail)
    (hskip : skip = couplingSkipAt boundary s t band a b i)
    (hready : RetainedCouplingReady P q w s t u band a b raw (embStk groupReg S))
    (hrows : (S.R 140).length = 2*band+1)
    (hpage : S.R 138 = cstream A w (if skip then [] else spatialCouplingCoefficientWords P q s t u band i)++pageTail)
    (hsrc : S.R 141 = cstream A w (spatialCouplingInputWords boundary t band a b i C)++tail)
    (rhs : GaussianInt) (rhsTail : List (Fin (A+4))) (hrhs : S.R 93 = csyms A w rhs++rhsTail)
    (hxs : ∀ x ∈ couplingInputWords boundary t band a b i C, Fits w x)
    (has : ∀ z ∈ couplingCoefficientWords P q s t u band i, Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ retainedGuardedPageSpatialCouplingRowCost skip q w band+1 ∧
      Exec body (retainedMaskedPageSpatialCouplingRow hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R 136 maskTail) 113
          (csyms A w (guardedCouplingRowWord P q t u band a b i boundary C rhs)++S.R 113)) 138 pageTail) 137
          ((cstream A w (if skip then [] else spatialCouplingCoefficientWords P q s t u band i)).reverse++S.R 137))}) := by
  let S₀ : Stacks 144 A := {S with R := Function.update S.R 136 maskTail}
  let v₀ : HS 144 Q A U := {v with flag := skip}
  have he₀ : Exec body (.act (.pop (.rt 136) (fun v o => {v with flag := pairRe (o.getD blank)}) .done))
      (mk v S) 1 (mk v₀ S₀) := by
    simpa [S₀,v₀,Action.run,update_rt,hmask,pairRe_pairSym (show 4 ≤ A by omega)] using
      Exec.act (body := body) (.pop (.rt 136) (fun v o => {v with flag := pairRe (o.getD blank)}) .done) (mk v S)
  have hready₀ : RetainedCouplingReady P q w s t u band a b raw (embStk groupReg S₀) := by
    rw [show embStk groupReg S₀ = embStk groupReg S from groupProject_updateR S 136 _ (by decide)]
    exact hready
  obtain ⟨v',m,hu,hm,he⟩ := retainedGuardedPageSpatialCouplingRow_prefix_exec (body := body)
    hQ boundary skip hA hw5 hqw hst hi C tail pageTail raw v₀ S₀ rfl hskip hready₀
    (by simpa [S₀] using hrows) (by simpa [S₀] using hpage) (by simpa [S₀] using hsrc) rhs rhsTail
    (by simpa [S₀] using hrhs) hxs has
  refine ⟨v',1+m,hu,by omega,(Exec.seq he₀ he).cast rfl ?_⟩
  rfl


theorem retainedMaskedPageSpatialCouplingRow_exec (hQ : SS.states ≤ Q) {P q w s t u band a b i : ℕ} [NeZero s]
    (boundary skip : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (hi : i < s)
    (C : ZMod s → GaussianInt) (tail pageTail raw : List (Fin (A+4)))
    (maskTail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hmask : S.R 136 = pairSym A skip skip::maskTail)
    (hskip : skip = couplingSkipAt boundary s t band a b i)
    (hready : RetainedCouplingReady P q w s t u band a b raw (embStk groupReg S))
    (hrows : (S.R 140).length = 2*band+1)
    (hpage : S.R 138 = cstream A w (if skip then [] else spatialCouplingCoefficientWords P q s t u band i)++pageTail)
    (hsrc : S.R 141 = cstream A w ((cyclicPaddedLine (fun j : ZMod s =>
      if j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
      then C j else 0) band).drop i)++tail)
    (rhs : GaussianInt) (rhsTail : List (Fin (A+4))) (hrhs : S.R 93 = csyms A w rhs++rhsTail)
    (hxs : ∀ x ∈ couplingInputWords boundary t band a b i C, Fits w x)
    (has : ∀ z ∈ couplingCoefficientWords P q s t u band i, Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ retainedGuardedPageSpatialCouplingRowCost skip q w band+1 ∧
      Exec body (retainedMaskedPageSpatialCouplingRow hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R 136 maskTail) 113
          (csyms A w (guardedCouplingRowWord P q t u band a b i boundary C rhs)++S.R 113)) 138 pageTail) 137
          ((cstream A w (if skip then [] else spatialCouplingCoefficientWords P q s t u band i)).reverse++S.R 137))}) := by
  let F := fun j : ZMod s => if j ∈
    (if boundary then haloBoundary s t band a b else haloInterior s t band a b) then C j else 0
  let source := cyclicPaddedLine F band
  let rest := cstream A w ((source.drop i).drop (2*band+1))++tail
  have hwindow : spatialCouplingInputWords boundary t band a b i C = (source.drop i).take (2*band+1) :=
    spatialCouplingInputWords_window boundary t band a b i C hi
  have hp : S.R 141 = cstream A w (spatialCouplingInputWords boundary t band a b i C)++rest := by
    rw [hsrc,hwindow]
    dsimp only [rest,source,F]
    rw [← List.append_assoc,← cstream_append,List.take_append_drop]
  exact retainedMaskedPageSpatialCouplingRow_prefix_exec (body := body)
    hQ boundary skip hA hw5 hqw hst hi C rest pageTail raw maskTail v S hmask hskip hready hrows hpage hp rhs rhsTail hrhs hxs has

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
