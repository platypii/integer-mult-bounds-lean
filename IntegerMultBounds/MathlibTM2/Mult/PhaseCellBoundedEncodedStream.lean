module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvExec

/-! An encoded output prefix carries a magnitude witness for its actual words. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

def EncodedRange (A w q e : ℕ) (xs : List (Fin (A+4))) : Prop :=
  ∃ zs : List GaussianInt, xs = cstream A w zs ∧ ∀ z ∈ zs, ‖value q z‖ ≤ (2 : ℝ)^e

structure BoundedEncodedStream (A w q e : ℕ) where
  val : List (Fin (A+4))
  bounded : EncodedRange A w q e val

instance {A w q e : ℕ} : CoeOut (BoundedEncodedStream A w q e) (List (Fin (A+4))) := ⟨fun xs => xs.val⟩

def boundedEncodedStream (A w q e : ℕ) (zs : List GaussianInt)
    (h : ∀ z ∈ zs, ‖value q z‖ ≤ (2 : ℝ)^e) : BoundedEncodedStream A w q e :=
  { val := cstream A w zs, bounded := ⟨zs,rfl,h⟩ }

@[simp] theorem boundedEncodedStream_coe (A w q e : ℕ) (zs : List GaussianInt)
    (h : ∀ z ∈ zs, ‖value q z‖ ≤ (2 : ℝ)^e) :
    (boundedEncodedStream A w q e zs h : List (Fin (A+4))) = cstream A w zs := rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
