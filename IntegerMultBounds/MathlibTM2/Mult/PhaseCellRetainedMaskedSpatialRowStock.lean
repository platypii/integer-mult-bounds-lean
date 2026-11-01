module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedMaskedPageSpatialCouplingRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedPageSpatialCouplingRowStock

/-! Read one active page row or copy an unobserved RHS, consuming one actual guard symbol. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem transferCountedLine_native {T Q A : ℕ} {P U : Type}
    (rows width src dst count saved tmp : Fin T) : mnNativePushBound 3
      (transferCountedLine (P := P) (Q := Q) (A := A) (U := U) rows width src dst count saved tmp) := by
  simp [transferCountedLine,unaryProduct,scanP,ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,
    transfer,transferAct,uclear,moveR,moveStep,whileR,peekR,popPush,mnNativePushBound,mnActPush]

theorem copyPrefix144_native {Q A : ℕ} {P U : Type} (count src dst saved tmp : Fin 144) :
    mnNativePushBound 3 (copyPrefix (P := P) (Q := Q) (A := A) (U := U) count src dst saved tmp) := by
  simp [copyPrefix,transfer,transferAct,copyR,copyStep,moveR,moveStep,scanR,drainR,popDo,keepIn,
    whileR,peekR,mnNativePushBound,mnActPush]

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

theorem retainedConsumePageSpatialCouplingRow_prefix_exec_within (hQ : SS.states ≤ Q) {P q w s t u band a b i : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (hi : i < s)
    (C : ZMod s → GaussianInt) (tail pageTail raw : List (Fin (A+4)))
    (K : ℕ) (hpush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ K)
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : RetainedCouplingReady P q w s t u band a b raw (embStk groupReg S))
    (hrows : (S.R 140).length = 2*band+1)
    (hpage : S.R 138 = cstream A w (spatialCouplingCoefficientWords P q s t u band i)++pageTail)
    (hsrc : S.R 141 = cstream A w (spatialCouplingInputWords boundary t band a b i C)++tail)
    (rhs : GaussianInt) (rhsTail : List (Fin (A+4))) (hrhs : S.R 93 = csyms A w rhs++rhsTail)
    (hxs : ∀ x ∈ couplingInputWords boundary t band a b i C, Fits w x)
    (has : ∀ z ∈ couplingCoefficientWords P q s t u band i, Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧ m ≤ retainedConsumePageSpatialCouplingRowCost w band ∧
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (realWeightWorkspace K w (2*band+1)+11000*(band+1)*(w+1))) depth
        (retainedConsumePageSpatialCouplingRow hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 113
          (csyms A w (couplingRowWord P q t u band a b i boundary C rhs)++S.R 113))
          138 pageTail) 137 ((cstream A w (spatialCouplingCoefficientWords P q s t u band i)).reverse++S.R 137))}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := retainedPageSpatialCouplingRow_prefix_exec_within (body := body)
    hQ boundary hA hw5 hqw hst hi C tail pageTail raw K hpush v S hready hrows hpage hsrc rhs rhsTail hrhs hxs has
  let S₁ : Stacks 144 A := {S with R := (Function.update S.R 113
    (csyms A w (couplingRowWord P q t u band a b i boundary C rhs)++S.R 113))}
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := transferCountedLine_exec (body := body)
    140 94 138 137 109 104 105 (by decide) (2*band+1) w
    (cstream A w (spatialCouplingCoefficientWords P q s t u band i)) pageTail (by simp)
    v₁ S₁ (by simpa [S₁] using hrows)
    (by simpa [S₁,embStk,groupReg] using hready.width) (by simpa [S₁] using hpage)
    (by simpa [S₁,embStk,groupReg] using hready.fresh 109 (by simp))
    (by simpa [S₁,embStk,groupReg] using hready.fresh 104 (by simp))
    (by simpa [S₁,embStk,groupReg] using hready.fresh 105 (by simp))
  exact ⟨v₂,m₁+m₂,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,(fun depth => by
      have ht₂ := mn_native_exec_within he₂ 3 (transferCountedLine_native ..) depth
        (mnSize (mk v₁ S₁)+depth+3*transferCountedLineCost (2*band+1) w)
        (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hm₂) _)
      exact (mn_seq_within_add (he₁ depth) ht₂).mono (by
        intro d z hz; dsimp only [transferCountedLineCost] at hz; nlinarith))⟩


theorem retainedGuardedPageSpatialCouplingRow_prefix_exec_within (hQ : SS.states ≤ Q) {P q w s t u band a b i : ℕ} [NeZero s]
    (boundary skip : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (hi : i < s)
    (C : ZMod s → GaussianInt) (tail pageTail raw : List (Fin (A+4)))
    (K : ℕ) (hpush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ K)
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
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (realWeightWorkspace K w (2*band+1)+12000*(band+1)*(w+1))) depth
        (retainedGuardedPageSpatialCouplingRow hQ) (mk v S) m
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
    intro depth
    simp only [guardedCouplingRowWord,← hskip,ite_true,cstream_nil,List.reverse_nil,List.nil_append]
    have ht := mn_native_exec_within he 3 (copyPrefix144_native ..) depth _ (Nat.le_refl _)
    have ht' : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (realWeightWorkspace K w (2*band+1)+12000*(band+1)*(w+1))) depth _ _ _ _ :=
      ht.mono (by intro d z hz; simp [csyms] at hz; nlinarith)
    have he' := ExecWithin.cond_true (q := retainedConsumePageSpatialCouplingRow hQ) hflag ht'
    refine he'.cast (by simp) ?_
    apply congrArg (mk v')
    refine Stacks.ext rfl rfl rfl ?_
    have hp : S.R 138 = pageTail := by simpa using hpage
    funext k
    by_cases h113 : k = 113 <;> by_cases h138 : k = 138 <;> by_cases h137 : k = 137 <;> simp_all
  | false =>
    obtain ⟨v',m,hu,hm,he⟩ := retainedConsumePageSpatialCouplingRow_prefix_exec_within (body := body)
      hQ boundary hA hw5 hqw hst hi C tail pageTail raw K hpush v S hready hrows (by simpa using hpage) hsrc
      rhs rhsTail hrhs hxs has
    refine ⟨v',m+1,hu,by simpa [retainedGuardedPageSpatialCouplingRowCost] using Nat.add_le_add_right hm 1,?_⟩
    intro depth
    simp only [guardedCouplingRowWord,← hskip,Bool.false_eq_true,ite_false]
    exact ExecWithin.cond_false hflag ((he depth).mono (by intro d z hz; nlinarith))


theorem retainedMaskedPageSpatialCouplingRow_prefix_exec_within (hQ : SS.states ≤ Q) {P q w s t u band a b i : ℕ} [NeZero s]
    (boundary skip : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (hi : i < s)
    (C : ZMod s → GaussianInt) (tail pageTail raw : List (Fin (A+4)))
    (maskTail : List (Fin (A+4)))
    (K : ℕ) (hpush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ K)
    (v : HS 144 Q A U) (S : Stacks 144 A)
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
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (realWeightWorkspace K w (2*band+1)+12000*(band+1)*(w+1))) depth
        (retainedMaskedPageSpatialCouplingRow hQ) (mk v S) m
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
  obtain ⟨v',m,hu,hm,he⟩ := retainedGuardedPageSpatialCouplingRow_prefix_exec_within (body := body)
    hQ boundary skip hA hw5 hqw hst hi C tail pageTail raw K hpush v₀ S₀ rfl hskip hready₀
    (by simpa [S₀] using hrows) (by simpa [S₀] using hpage) (by simpa [S₀] using hsrc) rhs rhsTail
    (by simpa [S₀] using hrhs) hxs has
  refine ⟨v',1+m,hu,by omega,?_⟩
  intro depth
  have ht₀ := mn_native_exec_within he₀ 0 (by simp [mnNativePushBound,mnActPush]) depth (mnSize (mk v S)+depth) (by simp)
  let Inv : ℕ → Store (HΓ (T := 144) A) (HS 144 Q A U) → Prop :=
    fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
      (realWeightWorkspace K w (2*band+1)+12000*(band+1)*(w+1))
  have hs : mnSize (mk v₀ S₀)+depth ≤ mnSize (mk v S)+depth := by
    simpa only [Nat.zero_mul,Nat.add_zero] using ht₀.final
  have hsize := Nat.le_of_add_le_add_right hs
  have ht₀' := ht₀.mono (J := Inv) (by
    intro d z hz
    change mnSize z+d ≤ mnSize (mk v S)+depth+
      (realWeightWorkspace K w (2*band+1)+12000*(band+1)*(w+1))
    exact Nat.le_trans hz (Nat.le_add_right _ _))
  have ht₁' := (he depth).mono (J := Inv) (by
    intro d z hz
    exact hz.trans (Nat.add_le_add_right (Nat.add_le_add_right hsize depth) _))
  exact ExecWithin.seq ht₀' ht₁'

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
