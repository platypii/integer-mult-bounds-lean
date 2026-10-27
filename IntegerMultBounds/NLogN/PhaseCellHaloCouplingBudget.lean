module

public import IntegerMultBounds.NLogN.PhaseCellHaloNeighborhood

/-! Charge expensive recovery rows only to the enlarged halo boundary, including artificial cuts. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {s t : ℕ} [NeZero s]

def haloCouplingGuardCost (s t band a b zeroCost rowCost : ℕ) [NeZero s] : ℕ :=
  (haloVertices s a b).sum (fun i => (if i ∈ haloInterior s t (2*band) a b then zeroCost else rowCost)+1)

theorem haloCouplingGuardCost_eq (band a b zeroCost rowCost : ℕ) :
    haloCouplingGuardCost s t band a b zeroCost rowCost =
      (haloInterior s t (2*band) a b).card*(zeroCost+1)+
        (haloBoundary s t (2*band) a b).card*(rowCost+1) := by
  have hI : (haloVertices s a b).filter (fun i => i ∈ haloInterior s t (2*band) a b) =
      haloInterior s t (2*band) a b := by
    ext i
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨haloInterior_subset s t (2*band) a b h,h⟩⟩
  have hB : (haloVertices s a b).filter (fun i => i ∉ haloInterior s t (2*band) a b) =
      haloBoundary s t (2*band) a b := by
    ext i
    simp [haloBoundary]
  have hsum : haloCouplingGuardCost s t band a b zeroCost rowCost =
      (haloVertices s a b).sum (fun i => if i ∈ haloInterior s t (2*band) a b then zeroCost+1 else rowCost+1) := by
    unfold haloCouplingGuardCost
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> rfl
  rw [hsum,Finset.sum_ite,hI,hB]
  simp

theorem haloCouplingGuardCost_le (hst : s < t) (band a b zeroCost rowCost : ℕ) :
    haloCouplingGuardCost s t band a b zeroCost rowCost ≤
      (b-a)*(zeroCost+1)+haloBoundaryCountBound s t (2*band) a b*(rowCost+1) := by
  rw [haloCouplingGuardCost_eq]
  exact Nat.add_le_add
    (Nat.mul_le_mul_right _ ((Finset.card_le_card (haloInterior_subset s t (2*band) a b)).trans
      (haloVertices_card_le s a b)))
    (Nat.mul_le_mul_right _ (haloBoundary_card_bound hst (2*band) a b))

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
