module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedPageSpatialCouplingRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedSpatialCouplingInputs
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

theorem retainedPageSpatialCouplingRow_packed_exec (hQ : SS.states ≤ Q) {P q w s t u band a b origin N j : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (_hst : s < t) (hfit : origin+N ≤ s) (hj : j < N)
    (C : ZMod s → GaussianInt) (tail pageTail raw : List (Fin (A+4)))
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : RetainedCouplingReady P q w s t u band a b raw (embStk groupReg S))
    (hrows : (S.R 140).length = 2*band+1)
    (hpage : S.R 138 = cstream A w (spatialCouplingCoefficientWords P q s t u band (origin+j))++pageTail)
    (hsrc : S.R 141 = cstream A w ((couplingSourceInterval boundary t band a b origin N C).drop j)++tail)
    (rhs : GaussianInt) (rhsTail : List (Fin (A+4))) (hrhs : S.R 93 = csyms A w rhs++rhsTail)
    (hxs : ∀ x ∈ couplingInputWords boundary t band a b (origin+j) C, Fits w x)
    (has : ∀ z ∈ couplingCoefficientWords P q s t u band (origin+j), Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧ m ≤ retainedPageSpatialCouplingRowCost w band ∧
      Exec body (retainedPageSpatialCouplingRow hQ) (mk v S) m
        (mk v' {S with R := (Function.update S.R 113
          (csyms A w (couplingRowWord P q t u band a b (origin+j) boundary C rhs)++S.R 113))}) := by
  let source := (couplingSourceInterval boundary t band a b origin N C).drop j
  let rest := cstream A w (source.drop (2*band+1))++tail
  have hwindow : source.take (2*band+1) = spatialCouplingInputWords boundary t band a b (origin+j) C :=
    couplingSourceInterval_window boundary t band a b origin N j C hfit hj
  have hp : S.R 141 = cstream A w (spatialCouplingInputWords boundary t band a b (origin+j) C)++rest := by
    rw [hsrc,← hwindow]
    dsimp only [rest,source]
    rw [← List.append_assoc,← cstream_append,List.take_append_drop]
  exact retainedPageSpatialCouplingRow_prefix_exec (body := body) hQ boundary hA hw5 hqw _hst (by omega)
    C rest pageTail raw v S hready hrows hpage hp rhs rhsTail hrhs hxs has

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
