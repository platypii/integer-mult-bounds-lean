module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPacketEncoding
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNumericalRoutingData

/-! Coefficient-level specifications of packed replica/key interchange. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer

def coefficientRealBits {N K L : ℕ} (w : ℕ) (f : Fin N → Fin K → Fin L → GaussianInt)
    (n : Fin N) (k : Fin K) (z : Fin (L*w)) : Bool :=
  let p := finProdFinEquiv.symm z
  ((f n k p.1).re : ZMod (2^w)).val.testBit p.2.val

def coefficientImagBits {N K L : ℕ} (w : ℕ) (f : Fin N → Fin K → Fin L → GaussianInt)
    (n : Fin N) (k : Fin K) (z : Fin (L*w)) : Bool :=
  let p := finProdFinEquiv.symm z
  ((f n k p.1).im : ZMod (2^w)).val.testBit p.2.val

/-- The forward router's input is the actual coefficient stream. -/
theorem cstream_replicaKeyWords {A N K L : ℕ} (w : ℕ)
    (f : Fin N → Fin K → Fin L → GaussianInt) :
    cstream A w (replicaKeyWords f) = replicaKeyWords (fun n k b =>
      pairSym A (coefficientRealBits w f n k b) (coefficientImagBits w f n k b)) := by
  simp only [cstream]
  rw [show csyms A w = (fun z => List.ofFn fun b : Fin w => pairSym A
    ((z.re : ZMod (2^w)).val.testBit b.val) ((z.im : ZMod (2^w)).val.testBit b.val)) by rfl]
  simpa only [coefficientRealBits,coefficientImagBits] using
    replicaKeyWords_encode f (fun z b => pairSym A
      ((z.re : ZMod (2^w)).val.testBit b.val) ((z.im : ZMod (2^w)).val.testBit b.val))

/-- The forward router's output is the same coefficients grouped by key. -/
theorem cstream_keyReplicaWords {A N K L : ℕ} (w : ℕ)
    (f : Fin N → Fin K → Fin L → GaussianInt) :
    cstream A w (keyReplicaWords f) = keyReplicaWords (fun n k b =>
      pairSym A (coefficientRealBits w f n k b) (coefficientImagBits w f n k b)) := by
  simp only [cstream]
  rw [show csyms A w = (fun z => List.ofFn fun b : Fin w => pairSym A
    ((z.re : ZMod (2^w)).val.testBit b.val) ((z.im : ZMod (2^w)).val.testBit b.val)) by rfl]
  simpa only [coefficientRealBits,coefficientImagBits] using
    keyReplicaWords_encode f (fun z b => pairSym A
      ((z.re : ZMod (2^w)).val.testBit b.val) ((z.im : ZMod (2^w)).val.testBit b.val))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
