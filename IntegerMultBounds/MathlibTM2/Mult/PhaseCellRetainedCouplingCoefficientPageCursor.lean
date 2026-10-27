module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedPageSpatialCouplingRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingCoefficientPageCursor

/-! Advance active coefficient rows into a saved prefix and restore that prefix after a pass. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

noncomputable def retainedConsumePageSpatialCouplingRow (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  .seq (retainedPageSpatialCouplingRow hQ) advanceCouplingCoefficientPage

def retainedConsumePageSpatialCouplingRowCost (w band : ℕ) : ℕ :=
  retainedPageSpatialCouplingRowCost w band+transferCountedLineCost (2*band+1) w

theorem retainedConsumePageSpatialCouplingRow_exec (hQ : SS.states ≤ Q) {P q w s t u band a b i : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (hi : i < s)
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
    ∃ v' m, v'.user = v.user ∧ m ≤ retainedConsumePageSpatialCouplingRowCost w band ∧
      Exec body (retainedConsumePageSpatialCouplingRow hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 113
          (csyms A w (couplingRowWord P q t u band a b i boundary C rhs)++S.R 113))
          138 pageTail) 137 ((cstream A w (spatialCouplingCoefficientWords P q s t u band i)).reverse++S.R 137))}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := retainedPageSpatialCouplingRow_exec (body := body)
    hQ boundary hA hw5 hqw hst hi C tail pageTail raw v S hready hrows hpage hsrc rhs rhsTail hrhs hxs has
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
  exact ⟨v₂,m₁+m₂,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
