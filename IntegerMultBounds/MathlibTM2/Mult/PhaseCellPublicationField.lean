module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationSelectLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationMaskHost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealPrefix
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellEncodedAmbient

/-! The selection mask chooses the interior or boundary word at each ambient coordinate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def publicationFlags (s t band a b : ℕ) : List Bool :=
  (List.range s).map (haloInteriorAt s t band a b)

def publicationField {s : ℕ} [NeZero s] (t band a b : ℕ)
    (D C : ZMod s → GaussianInt) (i : ZMod s) : GaussianInt :=
  if i ∈ haloInterior s t band a b then D i else C i

@[simp] theorem publicationFlags_length (s t band a b : ℕ) :
    (publicationFlags s t band a b).length = s := by simp [publicationFlags]

theorem publicationMaskSymbols_eq_flags (A s t band a b : ℕ) :
    publicationMaskSymbols A s t band a b =
      (publicationFlags s t band a b).map (fun flag => pairSym A flag flag) := by
  simp [publicationMaskSymbols,publicationFlags,List.map_map,Function.comp_def]

theorem publicationWords_chirpLine {A w s t band a b : ℕ} [NeZero s]
    (hst : s < t) (hbs : b ≤ s) (D C : ZMod s → GaussianInt) :
    publicationWords (publicationFlags s t band a b)
      ((chirpLine s D).map (csyms A w)) ((chirpLine s C).map (csyms A w)) =
      (chirpLine s (publicationField t band a b D C)).map (csyms A w) := by
  let flags := publicationFlags s t band a b
  let xs := (chirpLine s D).map (csyms A w)
  let ys := (chirpLine s C).map (csyms A w)
  have hx : xs.length = flags.length := by simp [xs,flags]
  have hy : ys.length = flags.length := by simp [ys,flags]
  apply List.ext_getElem
  · simp [publicationWords_length flags xs ys hx hy,xs,ys,flags]
  · intro i hi hj
    have his : i < s := by simpa [xs,ys,flags,publicationWords_length flags xs ys hx hy] using hi
    rw [publicationWords_getElem flags xs ys hx hy i (by simpa [flags] using his)]
    have hflag := haloInteriorAt_spec hst band a b i hbs his
    by_cases h : (i : ZMod s) ∈ haloInterior s t band a b
    · have hf : haloInteriorAt s t band a b i = true := hflag.mpr h
      simp [flags,xs,publicationFlags,chirpLine,publicationField,h,hf]
    · have hf : haloInteriorAt s t band a b i = false := Bool.eq_false_iff.mpr (fun hh => h (hflag.mp hh))
      simp [flags,ys,publicationFlags,chirpLine,publicationField,h,hf]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
