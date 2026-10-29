module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGuardedCouplingRowValue
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInterval

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem guardedCouplingRowWords_packed {s : ℕ} [NeZero s] (P q t u band a b origin N : ℕ)
    (boundary : Bool) (C B : ZMod s → GaussianInt) (hfit : origin+N ≤ s) :
    guardedCouplingRowWords P q t u band a b boundary C origin (packedInterval origin N B) =
      packedInterval origin N (guardedCouplingRowField P q t u band a b boundary C B) := by
  apply List.ext_getElem (by simp [packedInterval_length _ hfit])
  intro j hj hk
  have hjN : j < N := by simpa only [packedInterval_length _ hfit] using hk
  rw [guardedCouplingRowWords_getElem P q t u band a b origin boundary C
      (packedInterval origin N B) j (by simpa only [packedInterval_length _ hfit] using hjN),
    packedInterval_get B hfit hjN,packedInterval_get _ hfit hjN]
  simp only [guardedCouplingRowField,ZMod.val_natCast,Nat.mod_eq_of_lt (show origin+j < s by omega)]

/-- Cropping changes physical addresses, not the encoded coefficient word. -/
theorem packedInterval_decodeWord {s A : ℕ} [NeZero s] (w origin N j : ℕ)
    (F : ZMod s → GaussianInt) (hfit : origin+N ≤ s) (hj : j < N)
    (suffix packedSuffix : List (Fin (A+4))) :
    decodeWord (((cstream A w (packedInterval origin N F)++packedSuffix).drop (j*w)).take w) =
      decodeWord (((cstream A w (chirpLine s F)++suffix).drop ((origin+j)*w)).take w) := by
  rw [cstream_word w (packedInterval origin N F) packedSuffix j (by simpa [packedInterval_length _ hfit] using hj),
    cstream_word w (chirpLine s F) suffix (origin+j) (by simp; omega),packedInterval_get F hfit hj]
  simp [chirpLine]

/-- Prefix emission reverses word order; it does not reverse bits within a word. -/
theorem cstream_reverse_decodeWord {A : ℕ} (w : ℕ) (xs : List GaussianInt)
    (j : ℕ) (hj : j < xs.length) (suffix reverseSuffix : List (Fin (A+4))) :
    decodeWord (((cstream A w xs.reverse++reverseSuffix).drop ((xs.length-1-j)*w)).take w) =
      decodeWord (((cstream A w xs++suffix).drop (j*w)).take w) := by
  have hk : xs.length-1-j < xs.reverse.length := by simp only [List.length_reverse]; omega
  rw [cstream_word w xs.reverse reverseSuffix (xs.length-1-j) hk,
    cstream_word w xs suffix j hj]
  have hi : xs.length-1-(xs.length-1-j) = j := by omega
  simp only [List.getElem_reverse,List.length_reverse,hi]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
