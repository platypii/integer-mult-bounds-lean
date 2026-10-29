module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSpatialCouplingInputs

/-! A spatial source ribbon contains only the requested rows and stencil padding. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def couplingSourceInterval {s : ℕ} [NeZero s] (boundary : Bool) (t band a b origin N : ℕ)
    (C : ZMod s → GaussianInt) : List GaussianInt :=
  let T := if boundary then haloBoundary s t band a b else haloInterior s t band a b
  ((cyclicPaddedLine (fun j : ZMod s => if j ∈ T then C j else 0) band).drop origin).take (N+2*band)

theorem couplingSourceInterval_length {s : ℕ} [NeZero s] (boundary : Bool)
    (t band a b origin N : ℕ) (C : ZMod s → GaussianInt) (hfit : origin+N ≤ s) :
    (couplingSourceInterval boundary t band a b origin N C).length = N+2*band := by
  simp only [couplingSourceInterval,List.length_take,List.length_drop,cyclicPaddedLine,
    List.length_map,List.length_range]
  rw [Nat.min_eq_left (by omega)]

theorem couplingSourceInterval_length_le {s : ℕ} [NeZero s] (boundary : Bool)
    (t band a b origin N : ℕ) (C : ZMod s → GaussianInt) :
    (couplingSourceInterval boundary t band a b origin N C).length ≤ N+2*band := by
  simp only [couplingSourceInterval,List.length_take]
  exact Nat.min_le_left _ _

theorem couplingSourceInterval_window {s : ℕ} [NeZero s] (boundary : Bool)
    (t band a b origin N j : ℕ) (C : ZMod s → GaussianInt) (hfit : origin+N ≤ s) (hj : j < N) :
    ((couplingSourceInterval boundary t band a b origin N C).drop j).take (2*band+1) =
      spatialCouplingInputWords boundary t band a b (origin+j) C := by
  rw [spatialCouplingInputWords_window boundary t band a b (origin+j) C (by omega)]
  simp only [couplingSourceInterval,List.drop_take,List.drop_drop,List.take_take]
  rw [Nat.min_eq_left (by omega)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem copyPackedSpatialCouplingInputs_exec {P U : Type} {Q A s : ℕ} [NeZero s]
    {body : P → Pr P 144 Q A U} (boundary : Bool) (t band a b origin N j w : ℕ)
    (hfit : origin+N ≤ s) (hj : j < N) (C : ZMod s → GaussianInt)
    (tail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hrows : (S.R 102).length = 2*band+1) (hw : (S.R 94).length = w)
    (h109 : S.R 109 = []) (h104 : S.R 104 = []) (h105 : S.R 105 = [])
    (hsource : S.R 141 = cstream A w ((couplingSourceInterval boundary t band a b origin N C).drop j)++tail) :
    ∃ v' n, v'.user = v.user ∧ n ≤ copyCountedLineCost (2*band+1) w ∧
      Exec body copySpatialCouplingInputs (mk v S) n
        (mk v' {S with R := (Function.update S.R 110
          (cstream A w (spatialCouplingInputWords boundary t band a b (origin+j) C)++S.R 110))}) := by
  let words := spatialCouplingInputWords boundary t band a b (origin+j) C
  let source := (couplingSourceInterval boundary t band a b origin N C).drop j
  let rest := cstream A w (source.drop (2*band+1))++tail
  have hwindow : source.take (2*band+1) = words :=
    couplingSourceInterval_window boundary t band a b origin N j C hfit hj
  have hprefix : S.R 141 = cstream A w words++rest := by
    rw [hsource,← hwindow]
    dsimp only [rest,source]
    rw [← List.append_assoc,← cstream_append,List.take_append_drop]
  have hlen : (cstream A w words).length = (2*band+1)*w := by
    rw [length_cstream]
    have hh := (spatialCouplingInputWords_perm boundary t band a b (origin+j) C).length_eq
    simpa only [words,couplingInputWords_length] using congrArg (fun n => n*w) hh
  exact copyCountedLine_exec (body := body) 102 94 141 110 109 104 105 (by decide)
    (2*band+1) w (cstream A w words) rest hlen v S hrows hw hprefix h109 h104 h105

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
