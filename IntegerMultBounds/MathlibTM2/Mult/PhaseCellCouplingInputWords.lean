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

/-- Masking preserves any word property that also holds for zero. -/
theorem couplingInputWords_property {s : ℕ} [NeZero s] (boundary : Bool) (t band a b i : ℕ)
    (C : ZMod s → GaussianInt) (P : GaussianInt → Prop) (hzero : P 0)
    (hC : ∀ j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b), P (C j)) :
    ∀ z ∈ couplingInputWords boundary t band a b i C, P z := by
  intro z hz
  obtain ⟨δ,_,rfl⟩ := List.mem_map.mp hz
  let T := if boundary then haloBoundary s t band a b else haloInterior s t band a b
  let j : ZMod s := (i : ZMod s)+(δ : ZMod s)
  change P (if j ∈ T then C j else 0)
  by_cases hj : j ∈ T
  · simpa only [if_pos hj] using hC j hj
  · simpa only [if_neg hj] using hzero

theorem couplingInputWords_fits {s : ℕ} [NeZero s] (boundary : Bool) (t band a b i w : ℕ)
    (C : ZMod s → GaussianInt) (hC : ∀ j, Fast.Fits w (C j)) :
    ∀ z ∈ couplingInputWords boundary t band a b i C, Fast.Fits w z := by
  apply couplingInputWords_property boundary t band a b i C (Fast.Fits w)
  · constructor <;> simpa using (pow_pos (by decide : (0 : ℤ) < 2) (w-1))
  · intro j _
    exact hC j

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
