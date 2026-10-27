module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingRowValue
public import IntegerMultBounds.NLogN.PhaseCellSpatialCouplingOffsets

/-! Spatial operand order preserves the actual rounded coupling row, including wrapped aliases. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.ShortConv

def spatialCouplingInputWords {s : ℕ} [NeZero s] (boundary : Bool) (t band a b i : ℕ)
    (C : ZMod s → GaussianInt) : List GaussianInt :=
  let T := if boundary then haloBoundary s t band a b else haloInterior s t band a b
  (spatialCouplingOffsets band).map (fun δ : ℤ =>
    let j := (i : ZMod s)+(δ : ZMod s)
    if j ∈ T then C j else 0)

def spatialCouplingCoefficientWords (P q s t u band i : ℕ) : List GaussianInt :=
  (spatialCouplingOffsets band).map (fun δ : ℤ =>
    rationalWord q (PhaseCellCrossCell.entry P s t u band i ((i : ℤ)+δ)))

theorem spatialCouplingInputWords_perm {s : ℕ} [NeZero s] (boundary : Bool) (t band a b i : ℕ)
    (C : ZMod s → GaussianInt) :
    (spatialCouplingInputWords boundary t band a b i C).Perm (couplingInputWords boundary t band a b i C) :=
  (spatialCouplingOffsets_perm band).map _

theorem spatialCouplingCoefficientWords_perm (P q s t u band i : ℕ) :
    (spatialCouplingCoefficientWords P q s t u band i).Perm (couplingCoefficientWords P q s t u band i) :=
  (spatialCouplingOffsets_perm band).map _

theorem couplingRowWord_spatial {s : ℕ} [NeZero s] (P q t u band a b i : ℕ) (boundary : Bool)
    (C : ZMod s → GaussianInt) (rhs : GaussianInt) :
    rhs-(List.zipWith (fun x z => tdivN q (x*z)) (spatialCouplingInputWords boundary t band a b i C)
      (spatialCouplingCoefficientWords P q s t u band i)).sum =
      couplingRowWord P q t u band a b i boundary C rhs := by
  dsimp only [couplingRowWord,spatialCouplingInputWords,spatialCouplingCoefficientWords,
    couplingInputWords,couplingCoefficientWords]
  simp only [List.zipWith_map,List.zipWith_self]
  congr 1
  exact ((spatialCouplingOffsets_perm band).map _).sum_eq

theorem spatialCouplingInputWords_window {s : ℕ} [NeZero s] (boundary : Bool) (t band a b i : ℕ)
    (C : ZMod s → GaussianInt) (hi : i < s) :
    let T := if boundary then haloBoundary s t band a b else haloInterior s t band a b
    spatialCouplingInputWords boundary t band a b i C =
      ((cyclicPaddedLine (fun j => if j ∈ T then C j else 0) band).drop i).take (2*band+1) := by
  dsimp only [spatialCouplingInputWords]
  exact (cyclicPaddedLine_window
    (fun j : ZMod s => if j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b) then C j else 0)
    band i hi).symm

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
