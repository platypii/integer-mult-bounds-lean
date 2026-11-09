module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicColumnEntryStep
import Mathlib.Tactic.GCongr

/-! Uniform row-independent scalar bounds for cyclic table collection. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def cyclicEntryReadCostBound (V s w : ℕ) : ℕ :=
  ((s+s+s+s)*(4*V+10)+4*(8*V+12)+1+5*(4*V+4)+4*(8*V+8)+2)+
    (3*tblC V 0+((6*(s+s)+11*V+7)+(2*(5*V)+11)))+
    (((s+s)*(12*w+9)+10*w+22)+(2*(s+s)+2))

theorem cyclicEntryReadCost_le (V s a b i w : ℕ)
    (ha : a ≤ s) (hb : b ≤ s) (hi : i < s) :
    cyclicEntryReadCost V s a b i w ≤ cyclicEntryReadCostBound V s w := by
  have hj := (cyclicResidualIndex_lt (a := a) (b := b) hi).le
  dsimp [cyclicEntryReadCost,cyclicEntryReadCostBound]
  gcongr

def cyclicColumnEntryCostBound (q V s rowCount : ℕ) : ℕ :=
  (4*rowCount+4)+((rowCount*(12*V+11)+27*V+6*s+36)+((8*q+9)+
    (cyclicEntryReadCostBound V s (2*q+8)+(2*((2*q+8)+s)+5)))+1)

theorem cyclicColumnEntryStepCost_le (q V s a b n i rowCount : ℕ)
    (ha : a ≤ s) (hb : b ≤ s) (hn : n ≤ rowCount) (hi : i < s) :
    cyclicColumnEntryStepCost q V s a b n i ≤ cyclicColumnEntryCostBound q V s rowCount := by
  have hr := cyclicEntryReadCost_le V s a b i (2*q+8) ha hb hi
  dsimp [cyclicColumnEntryStepCost,selectedCyclicColumnEntryCost,cyclicColumnEntryCostBound]
  gcongr

/-- Every position in a clipped band uses the same cap; no row enumeration is needed. -/
theorem cyclicBandEntryStepCost_le {s : ℕ} [NeZero s] (B : Finset (ZMod s))
    (q V a b W n i : ℕ) (ha : a ≤ s) (hb : b ≤ s)
    (hi : i < min B.card (n+W+1)-(n-W)) :
    cyclicColumnEntryStepCost q V s a b (n-W+i) (bFoldAt s B (n-W+i)).val ≤
      cyclicColumnEntryCostBound q V s B.card := by
  apply cyclicColumnEntryStepCost_le q V s a b (n-W+i) _ B.card ha hb
  · omega
  · exact (bFoldAt s B (n-W+i)).val_lt

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
