module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSpatialCouplingWords
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyCountedLine

/-! Copy the spatial stencil from an already positioned source cursor. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 144 Q A U}

def copySpatialCouplingInputs : Pr P 144 Q A U := copyCountedLine 102 94 141 110 109 104 105

theorem copySpatialCouplingInputs_exec {s : ℕ} [NeZero s] (boundary : Bool)
    (t band a b i w : ℕ) (hi : i < s) (C : ZMod s → GaussianInt)
    (tail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hrows : (S.R 102).length = 2*band+1) (hw : (S.R 94).length = w)
    (h109 : S.R 109 = []) (h104 : S.R 104 = []) (h105 : S.R 105 = []) :
    let T := if boundary then haloBoundary s t band a b else haloInterior s t band a b
    let source := cyclicPaddedLine (fun j : ZMod s => if j ∈ T then C j else 0) band
    S.R 141 = cstream A w (source.drop i)++tail →
    ∃ v' n, v'.user = v.user ∧ n ≤ copyCountedLineCost (2*band+1) w ∧
      Exec body copySpatialCouplingInputs (mk v S) n
        (mk v' {S with R := (Function.update S.R 110
          (cstream A w (spatialCouplingInputWords boundary t band a b i C)++S.R 110))}) := by
  dsimp only
  intro hsource
  let T := if boundary then haloBoundary s t band a b else haloInterior s t band a b
  let source := cyclicPaddedLine (fun j : ZMod s => if j ∈ T then C j else 0) band
  let words := spatialCouplingInputWords boundary t band a b i C
  let rest := cstream A w ((source.drop i).drop (2*band+1))++tail
  have hwindow : words = (source.drop i).take (2*band+1) :=
    spatialCouplingInputWords_window boundary t band a b i C hi
  have hprefix : S.R 141 = cstream A w words++rest := by
    rw [hsource,hwindow]
    dsimp only [rest]
    rw [← List.append_assoc,← cstream_append,List.take_append_drop]
  have hlen : (cstream A w words).length = (2*band+1)*w := by
    rw [length_cstream]
    have hh := (spatialCouplingInputWords_perm boundary t band a b i C).length_eq
    simpa only [words,couplingInputWords_length] using congrArg (fun n => n*w) hh
  exact copyCountedLine_exec (body := body) 102 94 141 110 109 104 105 (by decide)
    (2*band+1) w (cstream A w words) rest hlen v S hrows hw hprefix h109 h104 h105

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
