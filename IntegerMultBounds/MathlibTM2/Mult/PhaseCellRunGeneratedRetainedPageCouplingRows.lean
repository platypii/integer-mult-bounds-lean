module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRunRetainedPageCouplingRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCouplingCounters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReversePrefixInPlace

/-! Generate the whole-line row clock, execute every coupling row and publish
in natural coordinate order, releasing the clock and current index. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def couplingCounterBank {A : ℕ} (q w : ℕ) (S : Stacks 144 A) : Stacks 144 A :=
  {S with R := (Function.update (Function.update (Function.update S.R
    (groupReg (cr .wn)) (List.replicate w tick)) (groupReg (cr .pn)) (List.replicate q tick))
      (groupReg (cr .nn)) (List.replicate (Schoenhage.Schedule.topN w) tick))}

theorem couplingCounterBank_ovr {A : ℕ} (q w : ℕ) (S : Stacks 144 A) :
    embOvr groupReg ({embStk groupReg S with R := counterR q w (embStk groupReg S).R} : Stacks 117 A).get S =
      couplingCounterBank q w S := by
  let T := embStk groupReg S
  let T₁ : Stacks 117 A := {T with R := Function.update T.R (cr .wn) (List.replicate w tick)}
  let T₂ : Stacks 117 A := {T₁ with R := Function.update T₁.R (cr .pn) (List.replicate q tick)}
  change embOvr groupReg ({T₂ with R := (Function.update T₂.R (cr .nn)
    (List.replicate (Schoenhage.Schedule.topN w) tick))} : Stacks 117 A).get S = _
  rw [embOvr_updR groupReg_injective]
  dsimp only [T₂]
  rw [embOvr_updR groupReg_injective]
  dsimp only [T₁]
  rw [embOvr_updR groupReg_injective,embOvr_stk]
  rfl

def retainedCouplingCounterPorts : List (Fin 144) := [groupReg (cr .wn),groupReg (cr .pn),groupReg (cr .nn)]

noncomputable def runGeneratedRetainedPageCouplingRows (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  .seq (embProg groupReg Empty.elim (couplingReadiness (P₀ := Empty)))
    (.seq (runRetainedPageCouplingRows hQ) (clearWords retainedCouplingCounterPorts))

def runGeneratedRetainedPageCouplingRowsCost (boundary : Bool) (q w s t band a b Nwords : ℕ) : ℕ :=
  (prepareCost q w+6*q+4*band+10)+runRetainedPageCouplingRowsCost boundary q w s t band a b Nwords+
    (2*(w+q+Schoenhage.Schedule.topN w)+7)

theorem runGeneratedRetainedPageCouplingRows_exec (hQ : SS.states ≤ Q) {P q w s t u band a b : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t)
    (C : ZMod s → GaussianInt) (rhs : List GaussianInt) (hlen : rhs.length = s)
    (tail pageTail maskTail rhsTail raw : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b raw (embStk groupReg S))
    (hsource : S.R 141 = cstream A w (cyclicPaddedLine (fun j : ZMod s =>
      if j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
      then C j else 0) band)++tail)
    (hmask : S.R 136 = couplingGuardSymbols boundary A s t band a b++maskTail)
    (hindex : S.R 107 = []) (hrhs : S.R 93 = cstream A w rhs++rhsTail)
    (h143 : S.R 143 = [])
    (hrows : (S.R 140).length = 2*band+1)
    (hpage : S.R 138 = cstream A w (couplingCoefficientPage P q s t u band a b s)++pageTail)
    (hwordCount : (S.R 139).length = (couplingCoefficientPage P q s t u band a b s).length)
    (hxs : ∀ j < s, ∀ x ∈ couplingInputWords boundary t band a b j C, Fits w x)
    (has : ∀ j < s, ∀ z ∈ couplingCoefficientWords P q s t u band j, Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧ m ≤ runGeneratedRetainedPageCouplingRowsCost boundary q w s t band a b
      (couplingCoefficientPage P q s t u band a b s).length ∧
      Exec (body) (runGeneratedRetainedPageCouplingRows hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 136 maskTail) 93 rhsTail)
          113 (cstream A w (guardedCouplingRowWords P q t u band a b boundary C 0 rhs)++S.R 113))}) := by
  obtain ⟨vi,n₁,hui,hn₁,hei,hcounter⟩ := retainedCouplingCounters_exec
    (body := fun p : Empty => nomatch p) q w hw5 hqw raw (embDn groupReg v) (embStk groupReg S) hready
  obtain ⟨v₁,hv₁,hu₁,he₁⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    groupReg_injective (fun p => nomatch p) hei v rfl S rfl
  rw [couplingCounterBank_ovr] at he₁
  let S₁ := couplingCounterBank q w S
  have hview : embStk groupReg S₁ = {embStk groupReg S with R := counterR q w (embStk groupReg S).R} := by
    change embStk groupReg (couplingCounterBank q w S) = _
    rw [← couplingCounterBank_ovr,embStk_ovr groupReg_injective]
  have hready₁ : RetainedCouplingReady P q w s t u band a b raw (embStk groupReg S₁) := by
    rw [hview]; exact hcounter
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := runRetainedPageCouplingRows_exec (body := body)
    hQ boundary hA hw5 hqw hst C rhs hlen tail pageTail maskTail rhsTail raw v₁ S₁ hready₁
    (by simpa [S₁,couplingCounterBank,groupReg,cr,OutputPlacement.code] using hsource)
    (by simpa [S₁,couplingCounterBank,groupReg,cr,OutputPlacement.code] using hmask)
    (by simpa [S₁,couplingCounterBank,groupReg,cr,OutputPlacement.code] using hindex)
    (by simpa [S₁,couplingCounterBank,groupReg,cr,OutputPlacement.code] using hrhs)
    (by simpa [S₁,couplingCounterBank,groupReg,cr,OutputPlacement.code] using h143)
    (by simpa [S₁,couplingCounterBank,groupReg,cr,OutputPlacement.code] using hrows)
    (by simpa [S₁,couplingCounterBank,groupReg,cr,OutputPlacement.code] using hpage)
    (by simpa [S₁,couplingCounterBank,groupReg,cr,OutputPlacement.code] using hwordCount) hxs has
  let result := cstream A w (guardedCouplingRowWords P q t u band a b boundary C 0 rhs)
  let S₂ : Stacks 144 A := {S₁ with R := (Function.update (Function.update (Function.update S₁.R
    136 maskTail) 93 rhsTail) 113 (result++S.R 113))}
  have h113 : S₁.R 113 = S.R 113 := by simp [S₁,couplingCounterBank,groupReg,cr,OutputPlacement.code]
  have he₂' : Exec body (runRetainedPageCouplingRows hQ) (mk v₁ S₁) n₂ (mk v₂ S₂) := by
    simpa only [h113] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) retainedCouplingCounterPorts (by decide) v₂ S₂
  have hlenCounters : (retainedCouplingCounterPorts.map fun k => (S₂.R k).length).sum =
      w+q+Schoenhage.Schedule.topN w := by
    simp [retainedCouplingCounterPorts,S₂,S₁,couplingCounterBank,groupReg,cr,OutputPlacement.code]
    ring
  have hwn : S.R (groupReg (cr .wn)) = [] := hready.arithmetic .wn
  have hpn : S.R (groupReg (cr .pn)) = [] := hready.arithmetic .pn
  have hnn : S.R (groupReg (cr .nn)) = [] := hready.arithmetic .nn
  have hfinal : {S₂ with R := fun k => if k ∈ retainedCouplingCounterPorts then [] else S₂.R k} =
      {S with R := (Function.update (Function.update (Function.update S.R 136 maskTail) 93 rhsTail)
        113 (result++S.R 113))} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hW : k = groupReg (cr .wn)
    · subst k; simpa [retainedCouplingCounterPorts,groupReg,cr,OutputPlacement.code] using hwn.symm
    by_cases hP : k = groupReg (cr .pn)
    · subst k; simpa [retainedCouplingCounterPorts,groupReg,cr,OutputPlacement.code] using hpn.symm
    by_cases hN : k = groupReg (cr .nn)
    · subst k; simpa [retainedCouplingCounterPorts,groupReg,cr,OutputPlacement.code] using hnn.symm
    simp only [retainedCouplingCounterPorts,List.mem_cons,List.not_mem_nil,or_false,hW,hP,hN,ite_false]
    simp only [S₂,S₁,couplingCounterBank]
    by_cases h136 : k = 136
    · subst k; simp [groupReg,cr,OutputPlacement.code]
    by_cases h93 : k = 93
    · subst k; simp [groupReg,cr,OutputPlacement.code]
    by_cases h113 : k = 113
    · subst k; simp [groupReg,cr,OutputPlacement.code]
    simp only [Function.update_of_ne h136,Function.update_of_ne h93,Function.update_of_ne h113,
      Function.update_of_ne hW,Function.update_of_ne hP,Function.update_of_ne hN]
  refine ⟨v₃,n₁+(n₂+(2*(w+q+Schoenhage.Schedule.topN w)+7)),hu₃.trans (hu₂.trans (hu₁.trans hui)),?_,
    (Exec.seq he₁ (Exec.seq he₂' he₃)).cast ?_ (congrArg (mk v₃) hfinal)⟩
  · dsimp only [runGeneratedRetainedPageCouplingRowsCost]
    omega
  · rw [hlenCounters]
    simp [retainedCouplingCounterPorts]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
