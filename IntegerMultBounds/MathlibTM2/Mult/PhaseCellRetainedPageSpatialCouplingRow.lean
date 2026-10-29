module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFinishCouplingCoefficientPage
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyCountedLine
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCountedCouplingInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCouplingArithmetic
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCouplingReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSpatialCouplingWords

/-! A spatial coupling row reads a retained coefficient-page prefix and restores it exactly. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellRationalArgs IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

noncomputable def retainedPageSpatialCouplingRow (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  .seq (copyCountedLine 140 94 138 111 109 104 105)
    (.seq (embProg (couplingViewReg 92 141) Empty.elim (prepareCountedCouplingInputs (P₀ := Empty)))
      (embProg groupReg Empty.elim (retainedCouplingRow (P := Empty) hQ)))

def retainedPageSpatialCouplingRowCost (w band : ℕ) : ℕ :=
  copyCountedLineCost (2*band+1) w+
    prepareCountedCouplingInputsCost band w+retainedCouplingRowCost (2*band+1) w

theorem retainedPageSpatialCouplingRow_prefix_exec (hQ : SS.states ≤ Q) {P q w s t u band a b i : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (_hst : s < t) (hi : i < s)
    (C : ZMod s → GaussianInt) (tail pageTail raw : List (Fin (A+4)))
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : RetainedCouplingReady P q w s t u band a b raw (embStk groupReg S))
    (hrows : (S.R 140).length = 2*band+1)
    (hpage : S.R 138 = cstream A w (spatialCouplingCoefficientWords P q s t u band i)++pageTail)
    (hsrc : S.R 141 = cstream A w (spatialCouplingInputWords boundary t band a b i C)++tail)
    (rhs : GaussianInt) (rhsTail : List (Fin (A+4))) (hrhs : S.R 93 = csyms A w rhs++rhsTail)
    (hxs : ∀ x ∈ couplingInputWords boundary t band a b i C, Fits w x)
    (has : ∀ z ∈ couplingCoefficientWords P q s t u band i, Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧ m ≤ retainedPageSpatialCouplingRowCost w band ∧
      Exec body (retainedPageSpatialCouplingRow hQ) (mk v S) m
        (mk v' {S with R := (Function.update S.R 113
          (csyms A w (couplingRowWord P q t u band a b i boundary C rhs)++S.R 113))}) := by
  let xs := spatialCouplingInputWords boundary t band a b i C
  let as := spatialCouplingCoefficientWords P q s t u band i
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := copyCountedLine_exec (body := body)
    140 94 138 111 109 104 105 (by decide) (2*band+1) w (cstream A w as) pageTail
    (by simp [as]) v S hrows hready.width hpage
    (hready.fresh 109 (by simp)) (hready.fresh 104 (by simp)) (hready.fresh 105 (by simp))
  let S₁ : Stacks 144 A := {S with R := Function.update S.R 111 (cstream A w as++S.R 111)}
  let e := couplingViewReg 92 141
  let rest := tail
  have hprefix : (embStk e S₁).R 92 = cstream A w xs++rest := by
    change S₁.R 141 = _
    simpa only [S₁,Function.update_of_ne (by decide : (141 : Fin 144) ≠ 111)] using hsrc
  have hxslen : xs.length = 2*band+1 := by simp [xs,spatialCouplingInputWords]
  have haslen : as.length = 2*band+1 := by simp [as]
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := prepareCountedCouplingInputs_exec
    (body := fun p : Empty => nomatch p) band w (cstream A w xs) rest (by simp [hxslen])
    (embDn e v₁) (embStk e S₁)
    (by simpa [S₁,e,couplingViewReg,embStk,groupReg] using hready.bandwidth)
    (by simpa [S₁,e,couplingViewReg,embStk,groupReg] using hready.width) hprefix
    (by simpa [S₁,e,couplingViewReg,embStk,groupReg] using hready.fresh 102 (by simp))
    (by simpa [S₁,e,couplingViewReg,embStk,groupReg] using hready.fresh 109 (by simp))
    (by simpa [S₁,e,couplingViewReg,embStk,groupReg] using hready.fresh 104 (by simp))
    (by simpa [S₁,e,couplingViewReg,embStk,groupReg] using hready.fresh 105 (by simp))
  obtain ⟨v₃,hv₃,hu₃,he₃⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    (couplingViewReg_injective 92 141 (by decide)) (fun p => nomatch p) he₂ v₁ rfl S₁ rfl
  let S₂ : Stacks 144 A := {S₁ with R := (Function.update (Function.update S₁.R 102
    (List.replicate (2*band+1) tick)) 110 (cstream A w xs++S₁.R 110))}
  have he₃' : Exec body (embProg e Empty.elim (prepareCountedCouplingInputs (P₀ := Empty)))
      (mk v₁ S₁) m₂ (mk v₃ S₂) := by
    convert he₃ using 1
    apply congrArg (mk v₃)
    let T := embStk e S₁
    let T₁ : Stacks 117 A := {T with R := Function.update T.R 102 (List.replicate (2*band+1) tick)}
    change _ = embOvr e ({T₁ with R := Function.update T₁.R 110 (cstream A w xs++T.R 110)} : Stacks 117 A).get S₁
    rw [embOvr_updR (couplingViewReg_injective 92 141 (by decide)) T₁,
      show T₁ = {T with R := Function.update T.R 102 (List.replicate (2*band+1) tick)} from rfl,
      embOvr_updR (couplingViewReg_injective 92 141 (by decide)),embOvr_stk]
    rfl
  let T := embStk groupReg S
  obtain ⟨v₄,m₄,hu₄,hm₄,he₄⟩ := retainedCouplingArithmetic_exec
    (body := fun p : Empty => nomatch p) hQ hA (by omega) (by omega) xs as rhs hxslen haslen
    (by intro x hx; exact hxs x ((spatialCouplingInputWords_perm boundary t band a b i C).mem_iff.mp hx))
    (by intro z hz; exact has z ((spatialCouplingCoefficientWords_perm P q s t u band i).mem_iff.mp hz))
    (embDn groupReg v₃) T rhsTail hready.width hrhs
    hready.clean hready.arithmetic hready.counters
    (hready.fresh 96 (by simp)) (hready.fresh 102 (by simp)) (hready.fresh 104 (by simp))
    (hready.fresh 105 (by simp)) (hready.fresh 106 (by simp)) (hready.fresh 108 (by simp))
    (hready.fresh 109 (by simp)) (hready.fresh 115 (by simp)) (hready.fresh 116 (by simp))
  have hview : embStk groupReg S₂ = {T with R := (Function.update (Function.update (Function.update T.R
      111 (cstream A w as++T.R 111)) 102 (List.replicate (2*band+1) tick)) 110 (cstream A w xs++T.R 110))} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    have hk := k.isLt
    by_cases h111 : k = 111 <;> by_cases h102 : k = 102 <;> by_cases h110 : k = 110 <;>
      simp_all [S₂,S₁,T,embStk,Function.comp_def,Function.update_apply,groupReg,Fin.ext_iff]
  obtain ⟨v₅,hv₅,hu₅,he₅⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    groupReg_injective (fun p => nomatch p) he₄ v₃ rfl S₂ hview
  refine ⟨v₅,m₁+(m₂+m₄),hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),
    by dsimp [retainedPageSpatialCouplingRowCost]; omega,
    (Exec.seq he₁ (Exec.seq he₃' he₅)).cast rfl ?_⟩
  apply congrArg (mk v₅)
  rw [embOvr_updR groupReg_injective]
  have hbase : embOvr groupReg T.get S₂ = S := by
    apply groupStacks_eq
    · rw [embStk_ovr groupReg_injective]
    · intro k hk
      exact (embOvr_off (e := groupReg) T.get S₂ (groupReg_off k hk)).1
    · intro k hk
      have hne (r : Fin 144) (hr : r.val < 117) : k ≠ r := by intro h; subst k; omega
      simpa [S₂,S₁,Function.update_apply,hne 110 (by decide),hne 111 (by decide),hne 102 (by decide)] using
        (embOvr_off (e := groupReg) T.get S₂ (groupReg_off k hk)).2
  rw [hbase]
  have hdot : rhs-(List.zipWith (fun x z => tdivN q (x*z)) xs as).sum =
      couplingRowWord P q t u band a b i boundary C rhs := by
    exact couplingRowWord_spatial P q t u band a b i boundary C rhs
  rw [hdot]
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases h113 : k = 113 <;> simp_all [T,embStk,groupReg]

theorem retainedPageSpatialCouplingRowCost_eq (w band : ℕ) :
    retainedPageSpatialCouplingRowCost w band =
      (2*band+1)*(rmulCost w+93*w+50)+30*w+4*band+129 := by
  dsimp only [retainedPageSpatialCouplingRowCost,copyCountedLineCost,prepareCountedCouplingInputsCost,
    retainedCouplingRowCost]
  ring


theorem retainedPageSpatialCouplingRow_exec (hQ : SS.states ≤ Q) {P q w s t u band a b i : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (_hst : s < t) (hi : i < s)
    (C : ZMod s → GaussianInt) (tail pageTail raw : List (Fin (A+4)))
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : RetainedCouplingReady P q w s t u band a b raw (embStk groupReg S))
    (hrows : (S.R 140).length = 2*band+1)
    (hpage : S.R 138 = cstream A w (spatialCouplingCoefficientWords P q s t u band i)++pageTail)
    (hsrc : S.R 141 = cstream A w ((cyclicPaddedLine (fun j : ZMod s =>
      if j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
      then C j else 0) band).drop i)++tail)
    (rhs : GaussianInt) (rhsTail : List (Fin (A+4))) (hrhs : S.R 93 = csyms A w rhs++rhsTail)
    (hxs : ∀ x ∈ couplingInputWords boundary t band a b i C, Fits w x)
    (has : ∀ z ∈ couplingCoefficientWords P q s t u band i, Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧ m ≤ retainedPageSpatialCouplingRowCost w band ∧
      Exec body (retainedPageSpatialCouplingRow hQ) (mk v S) m
        (mk v' {S with R := (Function.update S.R 113
          (csyms A w (couplingRowWord P q t u band a b i boundary C rhs)++S.R 113))}) := by
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
  exact retainedPageSpatialCouplingRow_prefix_exec (body := body) hQ boundary hA hw5 hqw _hst hi
    C rest pageTail raw v S hready hrows hpage hp rhs rhsTail hrhs hxs has

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
