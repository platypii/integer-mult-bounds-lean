module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySeamCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireCountedLine
import Mathlib.Tactic.Linarith

/-! Boundary publication and archive retirement cost linear ambient traffic.
Only ordinary scalar width is needed; neither bound depends on numerical rows. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

def boundaryPublicationTrafficFactor (cD : ℕ) : ℕ :=
  512*(cD+4)^2+106*cD+850

theorem boundarySeamCost_le_traffic (N p D s width W cD : ℕ)
    (hp : 1 ≤ p) (hps : p ≤ s) (hpW : p ≤ W) (hD : D ≤ cD*p)
    (hN : 1 ≤ N) (hw : 2*p+13 ≤ W) (hwidth : 0 < width) (hroom : 3*width < s) :
    boundarySeamCost N (2*p+13) D s width W ≤
      boundaryPublicationTrafficFactor cD*(N*(s*W)) := by
  have hcost := boundarySeamCost_le N (2*p+13) D s width W
    (hp.trans hps) (hp.trans hpW) hw hwidth hroom
  have htable : TableVM.tblC D 0 ≤ 32*(cD+4)^2*(s*W) := by
    have hfit : D+4 ≤ (cD+4)*p := by nlinarith only [hD,hp]
    have hsq := Nat.pow_le_pow_left hfit 2
    have hvol : p^2 ≤ s*W := by nlinarith only [hps,hpW]
    unfold TableVM.tblC
    nlinarith only [hsq,Nat.mul_le_mul_left (32*(cD+4)^2) hvol]
  have hvol : p ≤ s*W := hps.trans (Nat.le_mul_of_pos_right s (hp.trans hpW))
  have hlinear : D ≤ cD*(s*W) := hD.trans (Nat.mul_le_mul_left cD hvol)
  have htraffic : s*W ≤ N*(s*W) := Nat.le_mul_of_pos_left _ hN
  unfold boundaryPublicationTrafficFactor
  nlinarith only [hcost,htable,hlinear,htraffic]

theorem retireCountedLineCost_le_traffic (N R s L W : ℕ)
    (hrows : N*L ≤ s) (hL : 1 ≤ L) (hR : 1 ≤ R) (hW : 1 ≤ W) :
    retireCountedLineCost N (R*(L*W)) ≤ 21*(R*(s*W))+12 := by
  have hN : N ≤ s := (Nat.le_mul_of_pos_right N hL).trans hrows
  have htraffic : N ≤ R*(s*W) := hN.trans
    ((Nat.le_mul_of_pos_right s hW).trans (Nat.le_mul_of_pos_left _ hR))
  have hpayload : N*(R*(L*W)) ≤ R*(s*W) := by
    simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using Nat.mul_le_mul_left (R*W) hrows
  unfold retireCountedLineCost
  nlinarith only [htraffic,hpayload]

end IntegerMultBounds.MathlibTM2.Cost
