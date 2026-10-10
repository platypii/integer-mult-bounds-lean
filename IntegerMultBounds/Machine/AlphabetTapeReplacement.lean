import IntegerMultBounds.Machine.Alphabet
import IntegerMultBounds.Machine.SharedPlacementAlphabet

/-! Literal tape replacement commutes with the finite symbol encoding used
by lifted controllers. This preserves heads and every stationary tape. -/
namespace IntegerMultBounds.Machine.AlphabetTapeReplacement
variable {t a b : ℕ}

theorem map_setTape (e : Alphabet.Encoding a b) (v : Tapes t a) (i : Fin t)
    (f : ℤ → Fin (a+4)) (p : ℤ) :
    Alphabet.mapTapes e (SharedPlacementAlphabet.setTape v i f p)=
      SharedPlacementAlphabet.setTape (Alphabet.mapTapes e v) i (fun z => e.encode (f z)) p := by
  apply congrArg₂ Tapes.mk
  · rfl
  · funext j z
    by_cases h : j=i <;> simp [Alphabet.mapTapes,SharedPlacementAlphabet.setTape,h]

end IntegerMultBounds.Machine.AlphabetTapeReplacement
