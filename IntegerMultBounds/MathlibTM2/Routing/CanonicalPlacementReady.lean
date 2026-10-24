module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalPlacementResize

/-! Resizing preserves original dimension, reusable copy scratch and all tapes
outside the placement generator's finite workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
variable {T A : ℕ}

theorem canonicalPlacementResizedBank_base (R : Fin T → List (Fin (A+4)))
    (rg : Fin 49 → Fin T) (hrg : Function.Injective rg) (L n : ℕ)
    (hlarge : canonicalRouterStride n ≤ n) (k : Fin 3) (i : Fin 49)
    (hi : i.val < 34 ∨ 43 ≤ i.val) :
    canonicalPlacementResizedBank R rg L n hlarge k (rg i) =
      canonicalPlacementWidthBank R (rg ∘ canonicalPlacementResizeCore) L n (rg i) := by
  apply binaryResizeBatchBank_keep
  intro h
  obtain ⟨j,_,he⟩ := List.mem_map.mp h
  have hv := congrArg (fun x : Fin 49 => x.val) (hrg he)
  change 34+j.val = i.val at hv
  have := j.isLt
  omega

theorem canonicalPlacementResizedBank_copyReady (R : Fin T → List (Fin (A+4)))
    (rg : Fin 49 → Fin T) (hrg : Function.Injective rg) (L n : ℕ)
    (hlarge : canonicalRouterStride n ≤ n) (k : Fin 3) (i : Fin 49)
    (hi : i ∈ ([0,43,44,48] : List (Fin 49))) :
    canonicalPlacementResizedBank R rg L n hlarge k (rg i) = R (rg i) := by
  have hb : i.val < 34 ∨ 43 ≤ i.val := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> decide
  rw [canonicalPlacementResizedBank_base R rg hrg L n hlarge k i hb]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp [canonicalPlacementWidthBank,canonicalPlacementOperandBank,
      reservoirExchangeOperandBank,reservoirExchangeOperandJobs,canonicalGeometryBank,
      routerReservoirGeometryBank,routerGeometryBank,canonicalPlacementResizeCore,
      canonicalPlacementWidthCore,canonicalPlacementGeometrySlot,canonicalPlacementOperandSlot,
      routerReservoirCommonSlot,Function.comp_def,hrg.eq_iff]

theorem canonicalPlacementResizedBank_outside (R : Fin T → List (Fin (A+4)))
    (rg : Fin 49 → Fin T) (L n : ℕ) (hlarge : canonicalRouterStride n ≤ n) (k : Fin 3)
    (i : Fin T) (hoff : ∀ j, rg j ≠ i) :
    canonicalPlacementResizedBank R rg L n hlarge k i = R i := by
  rw [show canonicalPlacementResizedBank R rg L n hlarge k i =
      canonicalPlacementWidthBank R (rg ∘ canonicalPlacementResizeCore) L n i from by
    apply binaryResizeBatchBank_keep
    intro h
    obtain ⟨j,_,he⟩ := List.mem_map.mp h
    exact hoff _ he]
  have off (j : Fin 49) : i ≠ rg j := (hoff j).symm
  simp [canonicalPlacementWidthBank,canonicalPlacementOperandBank,
    reservoirExchangeOperandBank,reservoirExchangeOperandJobs,canonicalGeometryBank,
    routerReservoirGeometryBank,routerGeometryBank,Function.comp_def,off]

end IntegerMultBounds.MathlibTM2.Routing
