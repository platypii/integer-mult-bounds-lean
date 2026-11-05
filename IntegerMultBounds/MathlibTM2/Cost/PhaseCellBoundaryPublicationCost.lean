module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCallerBoundaryHeaderCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySeamCost
import Mathlib.Tactic.Linarith

/-! Publication adds scalar table work and linear stream traffic. The three
fixed crops share the same volume bound, independently of their contents. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Fast.TableVM

def boundaryPublicationTimeBound (N D s W : ℕ) : ℕ :=
  48*tblC D 0+350*D+1335*(N+1)*(s*W)+104

def boundaryPublicationStockBound (N D s W : ℕ) : ℕ :=
  208*tblC D 0+1426*D+5597*(N+1)*(s*W)+134

theorem boundarySeamHeaderVolume_le_traffic (p s width W D N : ℕ) (hs : 1 ≤ s)
    (hW : 2*p+13 ≤ W) :
    boundarySeamHeaderVolume p s width W D N ≤ 6*(N+1)*(s*W)+4*D := by
  have hWpos : 1 ≤ W := by omega
  have hSW : 1 ≤ s*W := Nat.mul_pos hs hWpos
  have hsW := Nat.le_mul_of_pos_right s hWpos
  have hWW := Nat.le_mul_of_pos_left W hs
  have hwW := hW.trans hWW
  have hN := Nat.le_mul_of_pos_right N hSW
  have hc := Nat.mul_le_mul_left (3*s) hW
  have hv := boundarySeamHeaderVolume_le p s width W D N
  nlinarith only [hv,hc,hsW,hWW,hwW,hN,Nat.zero_le (N*(s*W))]

theorem boundaryPublicationCosts_le (p s width W D N : ℕ) (hs : 1 ≤ s)
    (hw : 0 < width) (hroom : 3*width < s) (hW : 2*p+13 ≤ W) :
    (((6*boundarySeamHeaderVolume p s width W D N+67)+
        (3*boundarySeamBudget N D s W+1)+(2*boundarySeamHeaderVolume p s width W D N+23))+
        (2*boundaryTemporaryHeaderVolume p s width+13) ≤ boundaryPublicationTimeBound N D s W) ∧
    (2*(6*boundarySeamHeaderVolume p s width W D N+67)+13*boundarySeamBudget N D s W ≤
      boundaryPublicationStockBound N D s W) := by
  have hv := boundarySeamHeaderVolume_le_traffic p s width W D N hs hW
  have ht := boundaryTemporaryHeaderVolume_le p s width hs hw hroom
  have hwide := Nat.mul_le_mul_left (6*s) hW
  have hN : s*W ≤ (N+1)*(s*W) := Nat.le_mul_of_pos_left _ (by omega)
  unfold boundaryPublicationTimeBound boundaryPublicationStockBound boundarySeamBudget
  constructor <;> nlinarith only [hv,ht,hwide,hN]

end IntegerMultBounds.MathlibTM2.Cost
