module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInterval

/-! A borrowed suffix cannot change a read inside an encoded owned interval. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem packedIntervalRead_suffix {A s : ℕ} [NeZero s] (q w a N : ℕ)
    (F : ZMod s → GaussianInt) (tail tail' : List (Fin (A+4))) (hfit : a+N ≤ s)
    (i : ZMod s) (ha : a ≤ i.val) (hi : i.val < a+N) :
    packedIntervalRead q w a (cstream A w (packedInterval a N F)++tail) i =
      packedIntervalRead q w a (cstream A w (packedInterval a N F)++tail') i := by
  rw [packedIntervalRead_eq q w a N F tail [] hfit i ha hi,
    packedIntervalRead_eq q w a N F tail' [] hfit i ha hi]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
