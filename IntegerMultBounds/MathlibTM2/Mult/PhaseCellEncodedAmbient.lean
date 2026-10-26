module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellEncodedStream
public import IntegerMultBounds.MathlibTM2.Mult.ChirpCyclicMath

/-! Recover the ambient integer-field view from an exact encoded line. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem encodedStream_ambient {A w s : ℕ} [NeZero s] (hw : 0 < w)
    (E : List (Fin (A+4))) (hE : E.length = s*w)
    (hencoded : ∃ zs : List GaussianInt, E = cstream A w zs) :
    ∃ C : ZMod s → GaussianInt, E = cstream A w (chirpLine s C) := by
  obtain ⟨zs,rfl⟩ := hencoded
  have hzs : zs.length = s := Nat.mul_right_cancel hw (by simpa using hE)
  let C : ZMod s → GaussianInt := fun i => zs[i.val]'(by rw [hzs]; exact i.val_lt)
  have hline : chirpLine s C = zs := by
    apply List.ext_getElem (by simp [hzs])
    intro j hj _
    have hjs : j < s := by simpa using hj
    simp [chirpLine,C,Nat.mod_eq_of_lt hjs]
  exact ⟨C,by rw [hline]⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
