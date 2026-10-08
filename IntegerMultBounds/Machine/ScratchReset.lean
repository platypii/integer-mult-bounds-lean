import IntegerMultBounds.Machine.CountedErase
import IntegerMultBounds.Machine.CountedSeek

/-! Restore a scratch segment and its head after a stream writes it. Both
backward seeks, every erased cell, reusable clocks and sequential joins are
charged. The immutable length descriptor is an explicit prepared input. -/
namespace IntegerMultBounds.Machine.ScratchReset

abbrev bank := CountedSeek.bank

theorem erase_bank (f : ℤ → Fin 4) (p : ℤ) (bs : List Bool) :
    CountedErase.bank f p bs = bank f p bs := by
  unfold bank
  unfold CountedErase.bank CountedLoopReuse.bank CountedLoopReuse.controls
    CountedErase.one Tapes.append CountedSeek.bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

/-- Rewind from the end, erase forward, and rewind the clean segment. -/
def program : Program 3 50 0 :=
  seq (seq CountedSeek.backwardProgram CountedErase.program) CountedSeek.backwardProgram

theorem reset_hoare (f : ℤ → Fin 4) (p : ℤ) (bs : List Bool) :
    HoareTime program (fun v => v = bank f (p+Counter.value bs) bs)
      (fun v => v = bank (CountedErase.erased f p (Counter.value bs)) p bs)
      (17*Counter.value bs+21*bs.length+50) := by
  have h₀ := CountedSeek.seek_backward_hoare f (p+Counter.value bs) bs
  rw [add_sub_cancel_right] at h₀
  have h₁ := CountedErase.erase_hoare f p bs
  simp only [erase_bank] at h₁
  have h₂ := CountedSeek.seek_backward_hoare
    (CountedErase.erased f p (Counter.value bs)) (p+Counter.value bs) bs
  rw [add_sub_cancel_right] at h₂
  exact ((h₀.seq h₁).seq h₂).consequence (fun _ h => h) (fun _ h => h) (by omega)

/-- A scratch word over a blank interval is removed and its head returns to
its original position. Other cells and both control tapes are preserved. -/
theorem reset_word_hoare (f : ℤ → Fin 4) (p : ℤ) (xs : List (Fin 4))
    (bs : List Bool) (hcount : Counter.value bs = xs.length)
    (hblank : ∀ z, p ≤ z → z < p+xs.length → f z = blank) :
    HoareTime program (fun v => v = bank (putWord f p xs) (p+xs.length) bs)
      (fun v => v = bank f p bs) (17*xs.length+21*bs.length+50) := by
  have h := reset_hoare (putWord f p xs) p bs
  simpa only [hcount,CountedErase.erased_word f p xs hblank] using h

theorem reset_word_hoare_linear (f : ℤ → Fin 4) (p : ℤ) (xs : List (Fin 4))
    (bs : List Bool) (hcount : Counter.value bs = xs.length)
    (hblank : ∀ z, p ≤ z → z < p+xs.length → f z = blank)
    (hc : GrowingCounterData.Canonical bs) :
    HoareTime program (fun v => v = bank (putWord f p xs) (p+xs.length) bs)
      (fun v => v = bank f p bs) (38*xs.length+71) := by
  have hw := GrowingCounterData.canonical_width bs hc
  have hl := Nat.log2_le_self (Counter.value bs)
  exact (reset_word_hoare f p xs bs hcount hblank).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.ScratchReset
