module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingInputOffsetLoop
public import IntegerMultBounds.NLogN.PhaseCellCouplingOffsets

/-! Input word order agrees exactly with the alias-preserving coefficient row. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellRationalArgs

def couplingInputWords {s : ℕ} [NeZero s] (boundary : Bool) (t band a b i : ℕ)
    (C : ZMod s → GaussianInt) : List GaussianInt :=
  let T := if boundary then haloBoundary s t band a b else haloInterior s t band a b
  (couplingOffsets band).reverse.map (fun δ : ℤ =>
    let j : ZMod s := (i : ZMod s)+(δ : ZMod s)
    if j ∈ T then C j else 0)

theorem couplingInputWords_split {s : ℕ} [NeZero s] (boundary : Bool) (t band a b i : ℕ)
    (C : ZMod s → GaussianInt) :
    couplingInputWords boundary t band a b i C =
      couplingInputOffsetWords true boundary t band a b i band C ++
      couplingInputOffsetWords false boundary t band a b i band C ++
      [maskedCouplingInputWord false boundary t band a b i 0 C] := by
  simp [couplingInputWords,couplingOffsets,couplingInputOffsetWords,maskedCouplingInputWord,
    List.reverse_append,List.map_reverse,List.map_map,Function.comp_def,couplingOffset,List.append_assoc]

@[simp] theorem couplingInputWords_length {s : ℕ} [NeZero s] (boundary : Bool) (t band a b i : ℕ)
    (C : ZMod s → GaussianInt) : (couplingInputWords boundary t band a b i C).length = 2*band+1 := by
  simp [couplingInputWords]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
