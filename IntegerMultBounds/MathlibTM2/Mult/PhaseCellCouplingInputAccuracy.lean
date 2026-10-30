module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingInputWords
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightStream

/-! Decoding a generated masked input row preserves the original input error. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.PhaseCellMatrix

/-- Active-set norm bounds suffice for every gathered input word, including
wrapped stencil coordinates. Masked coordinates require no input bound. -/
theorem couplingInputWords_fits_of_norm {w q inputExp s : ℕ} [NeZero s]
    (boundary : Bool) (t band a b i : ℕ) (C : ZMod s → GaussianInt)
    (hw : q+inputExp+2 ≤ w)
    (hC : ∀ j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b),
      ‖value q (C j)‖ ≤ (2 : ℝ)^inputExp) :
    ∀ z ∈ couplingInputWords boundary t band a b i C, Fits w z := by
  apply couplingInputWords_property boundary t band a b i C (Fits w)
  · constructor <;> simp
  · intro j hj
    exact fits_of_value_power hw _ (hC j hj)

theorem couplingInputWords_decode {A w q inputExp s : ℕ} [NeZero s]
    (boundary : Bool) (t band a b i : ℕ) (C : ZMod s → GaussianInt) (x : ZMod s → ℝ) (ε : ℝ)
    (hA : 96 ≤ A) (hw : q+inputExp+2 ≤ w) (hε : 0 ≤ ε)
    (hC : ∀ j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b),
      ‖value q (C j)‖ ≤ (2 : ℝ)^inputExp)
    (hx : ∀ j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b),
      |(value q (C j)).re-x j| ≤ ε)
    (tail : List (Fin (A+4))) (n : ℕ) (hn : n < 2*band+1) :
    let j : ZMod s := (i : ZMod s)+(((couplingOffsets band).reverse.getD n 0 : ℤ) : ZMod s)
    let T := if boundary then haloBoundary s t band a b else haloInterior s t band a b
    |(value q (decodeWord (((cstream A w (couplingInputWords boundary t band a b i C)++tail).drop (n*w)).take w))).re-(if j ∈ T then x j else 0)| ≤ ε := by
  dsimp only
  let T := if boundary then haloBoundary s t band a b else haloInterior s t band a b
  let j : ZMod s := (i : ZMod s)+(((couplingOffsets band).reverse.getD n 0 : ℤ) : ZMod s)
  let z := if j ∈ T then C j else 0
  have hword : n < (couplingInputWords boundary t band a b i C).length := by simpa using hn
  have hoff : n < (couplingOffsets band).reverse.length := by simpa using hn
  rw [cstream_word w _ tail n hword]
  have hget : (couplingInputWords boundary t band a b i C)[n] = z := by
    dsimp only [z,j,T]
    simp only [couplingInputWords,List.getElem_map,List.getD_eq_getElem _ _ hoff]
  have hfit : Fits w z := by
    rw [← hget]
    exact couplingInputWords_fits_of_norm boundary t band a b i C hw hC _ (List.getElem_mem _)
  rw [hget,decodeWord_of_fits (by omega) (by omega) z hfit]
  change |(value q z).re-(if j ∈ T then x j else 0)| ≤ ε
  by_cases hmem : j ∈ T
  · simpa only [z,if_pos hmem] using hx j hmem
  · simpa [z,hmem,value] using hε

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
