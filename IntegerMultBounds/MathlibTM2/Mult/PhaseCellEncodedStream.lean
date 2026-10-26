module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! Encoded coefficient streams retain their integer-word witness. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

structure EncodedStream (A w : ℕ) where
  val : List (Fin (A+4))
  encoded : ∃ zs : List GaussianInt, val = cstream A w zs

instance {A w : ℕ} : CoeOut (EncodedStream A w) (List (Fin (A+4))) := ⟨EncodedStream.val⟩

def encodedStream (A w : ℕ) (zs : List GaussianInt) : EncodedStream A w :=
  ⟨cstream A w zs,⟨zs,rfl⟩⟩

@[simp] theorem encodedStream_coe (A w : ℕ) (zs : List GaussianInt) :
    (encodedStream A w zs : List (Fin (A+4))) = cstream A w zs := rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
