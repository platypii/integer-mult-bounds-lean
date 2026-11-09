module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedCyclicBandCollectionStock
import Mathlib.Tactic.GCongr

/-! Uniform clipped-band control and collection reserves. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

def scaledBandControls24CostBound (band rowCount : ℕ) : ℕ :=
  34*rowCount+16*(24*band+1)+4*band+56

theorem scaledBandControls24Cost_le (n band rowCount : ℕ) (hn : n ≤ rowCount) :
    scaledBandControlsCost 24 n band rowCount ≤ scaledBandControls24CostBound band rowCount := by
  unfold scaledBandControlsCost clippedBandControlsCost bandIntervalEndpointsCost clipUnaryCost
    scaledBandControls24CostBound
  simp only [List.sum_cons,List.sum_nil,Nat.add_zero]
  omega

@[irreducible] def cyclicCollectionUniformWorkspace (cap q band rowCount : ℕ) : ℕ :=
  25*scaledBandControls24CostBound band rowCount+(2*(24*band+1)+1)*((2*q+8)+1)+8*(cap+2)

theorem preparedCyclicBandCollectionWorkspace_le_uniform (cap q band rowCount n : ℕ)
    (hn : n ≤ rowCount) :
    preparedCyclicBandCollectionWorkspace cap q band rowCount n ≤
      cyclicCollectionUniformWorkspace cap q band rowCount := by
  have hc := scaledBandControls24Cost_le n band rowCount hn
  have hL : min rowCount (n+(24*band+1)+1)-(n-(24*band+1)) ≤ 2*(24*band+1)+1 := by omega
  unfold preparedCyclicBandCollectionWorkspace cyclicCollectionUniformWorkspace
  gcongr

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
