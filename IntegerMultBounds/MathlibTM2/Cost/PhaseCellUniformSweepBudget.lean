module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUniformPublicationSetup
import Mathlib.Tactic.Linarith

/-! Uniform publication controls and their owned count are linear traffic.
No table-width factor or origin packet occurs in this lifecycle. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem uniformPublicationSetupCosts_le (N L W traffic : ℕ)
    (hvolume : N*(L*W) ≤ traffic) (hcount : N ≤ traffic) (hpacket : L*W ≤ traffic)
    (hW : 1 ≤ W) (htraffic : 1 ≤ traffic) :
    PreparedPublicationPlan.uniformSetupCost N L W+(2*(N*(L*W))+4*N+2*(L*W)+9) ≤ 120*traffic ∧
      2*PreparedPublicationPlan.uniformSetupCost N L W ≤ 120*traffic := by
  have hL : L ≤ L*W := Nat.le_mul_of_pos_right L hW
  unfold PreparedPublicationPlan.uniformSetupCost uniformSweepControlsCost
  constructor <;> nlinarith only [hvolume,hcount,hpacket,hL,htraffic]

end IntegerMultBounds.MathlibTM2.Cost
