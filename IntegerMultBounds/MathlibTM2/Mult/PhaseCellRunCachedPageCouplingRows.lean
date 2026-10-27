module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRunPreparedPageCouplingRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBuildCouplingPageCache

/-! Copy retained guards linearly, execute one cached coupling pass, and restore both retained pages. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

noncomputable def runCachedPageCouplingRows (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  .seq (copyPrefix 97 135 136 104 105) (runPreparedPageCouplingRows hQ)

def runCachedPageCouplingRowsCost (boundary : Bool) (q w s t band a b Nwords : ℕ) : ℕ :=
  10*s+10+runPreparedPageCouplingRowsCost boundary q w s t band a b Nwords

theorem runCachedPageCouplingRows_exec (hQ : SS.states ≤ Q) {P q w s t u band a b : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t)
    (C : ZMod s → GaussianInt) (rhs : List GaussianInt) (hlen : rhs.length = s)
    (tail pageTail rhsTail raw : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b raw (embStk groupReg S))
    (hsource : S.R 141 = cstream A w (cyclicPaddedLine (fun j : ZMod s =>
      if j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
      then C j else 0) band)++tail)
    (hguard : S.R 135 = couplingGuardSymbols true A s t band a b)
    (hindex : S.R 107 = []) (hrhs : S.R 93 = cstream A w rhs++rhsTail)
    (h143 : S.R 143 = [])
    (hrows : (S.R 140).length = 2*band+1)
    (hpage : S.R 138 = cstream A w (couplingCoefficientPage P q s t u band a b s)++pageTail)
    (hwordCount : (S.R 139).length = (couplingCoefficientPage P q s t u band a b s).length)
    (hxs : ∀ j < s, ∀ x ∈ couplingInputWords boundary t band a b j C, Fits w x)
    (has : ∀ j < s, ∀ z ∈ couplingCoefficientWords P q s t u band j, Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧ m ≤ runCachedPageCouplingRowsCost boundary q w s t band a b
      (couplingCoefficientPage P q s t u band a b s).length ∧
      Exec (body) (runCachedPageCouplingRows hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 93 rhsTail)
          113 (cstream A w (guardedCouplingRowWords P q t u band a b boundary C 0 rhs)++S.R 113))}) := by
  let flags := couplingGuardSymbols true A s t band a b
  obtain ⟨v₁,hu₁,he₁⟩ := copyPrefix_exec (body := body) (count := 97) (src := 135) (dst := 136)
    (saved := 104) (tmp := 105) (by decide) v S flags [] (by simpa [flags] using hguard)
    (by simpa [flags,embStk,groupReg] using hready.axis) (hready.fresh 104 (by simp)) (hready.fresh 105 (by simp))
  let G : Stacks 144 A := {S with R := Function.update S.R 136 (flags++S.R 136)}
  have he₁' : Exec body (copyPrefix 97 135 136 104 105) (mk v S) (10*s+10) (mk v₁ G) := by
    simpa [flags,G] using he₁
  have hreadyG : CouplingReady P q w s t u band a b raw (embStk groupReg G) := by
    rw [show embStk groupReg G = embStk groupReg S from groupProject_updateR S 136 _ (by decide)]
    exact hready
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := runPreparedPageCouplingRows_exec (body := body)
    hQ boundary hA hw5 hqw hst C rhs hlen tail pageTail (S.R 136) rhsTail raw v₁ G hreadyG
    (by simpa [G] using hsource) (by rfl) (by simpa [G] using hindex)
    (by simpa [G] using hrhs) (by simpa [G] using h143)
    (by simpa [G] using hrows) (by simpa [G] using hpage) (by simpa [G] using hwordCount) hxs has
  refine ⟨v₂,(10*s+10)+m₂,hu₂.trans hu₁,Nat.add_le_add_left hm₂ _,(Exec.seq he₁' he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases h136 : k = 136 <;> simp [G,h136,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
