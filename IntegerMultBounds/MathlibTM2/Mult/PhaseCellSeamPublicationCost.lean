module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCorePublication
public import IntegerMultBounds.NLogN.PhaseCellCoreWindowCost

/-! The existing restoring full-line slice pays an ambient traversal for each
exceptional core. There are at most three such cores. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.NLogN.PhaseCellMatrix
open scoped BigOperators

/-- Bound the exact time in `publishOwnedCore_exec`, including prefix traversal. -/
theorem publishOwnedCore_cost_le (s width k W : ℕ) (hstart : coreStart width k ≤ s) :
    6*(coreStart width k*W)+10*(coreLength s width k*W)+16 ≤ 10*(s*W)+16 := by
  have hlen : coreLength s width k ≤ s-coreStart width k := min_le_right _ _
  have htotal : coreStart width k+coreLength s width k ≤ s := by omega
  have hm := Nat.mul_le_mul_right W htotal
  rw [Nat.add_mul] at hm
  omega

/-- The complete exceptional slice bill is at most three ambient traversals.
This charges actual generated indices, including the clipped final core. -/
theorem seamPublication_cost_le (s width radius W : ℕ) (hr : radius ≤ width)
    (hstarts : ∀ k ∈ coreIndices s width, coreStart width k ≤ s) :
    let seams := ((coreIndices s width).toFinset).filter (fun k =>
      ¬ (radius ≤ coreStart width k ∧ coreStart width k+coreLength s width k+radius ≤ s))
    (∑ k ∈ seams, (6*(coreStart width k*W)+10*(coreLength s width k*W)+16)) ≤
      30*(s*W)+48 := by
  dsimp only
  let seams := ((coreIndices s width).toFinset).filter (fun k =>
    ¬ (radius ≤ coreStart width k ∧ coreStart width k+coreLength s width k+radius ≤ s))
  change (∑ k ∈ seams, (6*(coreStart width k*W)+10*(coreLength s width k*W)+16)) ≤ 30*(s*W)+48
  have hc : seams.card ≤ 3 := coreHalo_fallback_count s width radius hr
  have hb : (∑ k ∈ seams, (6*(coreStart width k*W)+10*(coreLength s width k*W)+16)) ≤
      seams.card*(10*(s*W)+16) := by
    calc
      _ ≤ ∑ _k ∈ seams, (10*(s*W)+16) := Finset.sum_le_sum (fun k hk =>
        publishOwnedCore_cost_le s width k W (hstarts k (List.mem_toFinset.mp (Finset.mem_filter.mp hk).1)))
      _ = _ := by simp
  have hm := Nat.mul_le_mul_right (10*(s*W)+16) hc
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
