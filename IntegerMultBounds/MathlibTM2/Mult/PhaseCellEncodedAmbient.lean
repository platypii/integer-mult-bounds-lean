module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpCyclicMath

/-! Recover the ambient integer-field view from an exact encoded line. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def ambientOfWords {s : ℕ} [NeZero s] (zs : List GaussianInt) (hlen : zs.length = s) : ZMod s → GaussianInt :=
  fun i => zs[i.val]'(by rw [hlen]; exact i.val_lt)

theorem chirpLine_ambientOfWords {s : ℕ} [NeZero s] (zs : List GaussianInt) (hlen : zs.length = s) :
    chirpLine s (ambientOfWords zs hlen) = zs := by
  apply List.ext_getElem (by simp [hlen])
  intro j hj _
  have hjs : j < s := by simpa using hj
  simp [chirpLine,ambientOfWords,Nat.mod_eq_of_lt hjs]

theorem ambientOfWords_mem {s : ℕ} [NeZero s] (zs : List GaussianInt) (hlen : zs.length = s) (i : ZMod s) :
    ambientOfWords zs hlen i ∈ zs := List.getElem_mem _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
