module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightTableStream
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairLayout

/-! Exact single-cell weight page in the runtime coordinate orders. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN

def ambientWeightSample (P s t u lo i : ℕ) : ℚ :=
  PhaseCellConcreteCoefficients.similarity P s t u ((lo + i) % s : ℕ)

def weightPage (A w q P s t u lo L : ℕ) : List (Fin (A + 4)) :=
  cstream A w ((List.range L).reverse.map (fun i => rationalWord q (ambientWeightSample P s t u lo i))) ++
    cstream A w ((List.range L).map (fun i => reciprocalWeightWord q (ambientWeightSample P s t u lo i)))

@[simp] theorem weightPage_length (A w q P s t u lo L : ℕ) :
    (weightPage A w q P s t u lo L).length = 2 * L * w := by
  simp [weightPage]
  ring

def outputWeightRow (A w q P s t u L lo : ℕ) : List (Fin (A + 4)) :=
  cstream A w ((List.range L).reverse.map (fun i => rationalWord q (ambientWeightSample P s t u lo i)))

def inputWeightRow (A w q P s t u L lo : ℕ) : List (Fin (A + 4)) :=
  cstream A w ((List.range L).map (fun i => reciprocalWeightWord q (ambientWeightSample P s t u lo i)))

@[simp] theorem outputWeightRow_length (A w q P s t u L lo : ℕ) :
    (outputWeightRow A w q P s t u L lo).length = L * w := by simp [outputWeightRow]

@[simp] theorem inputWeightRow_length (A w q P s t u L lo : ℕ) :
    (inputWeightRow A w q P s t u L lo).length = L * w := by simp [inputWeightRow]

/-- The tape evaluator uses exactly the original ambient phase coordinate. -/
theorem ambientWeightSample_eq_weightData (s t p u : ℕ) [NeZero s] (lo : ZMod s) (i : ℕ) :
    ambientWeightSample (2 ^ 15 * p) s t u lo.val i = weightData s t p u lo i := by
  unfold ambientWeightSample weightData
  rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
