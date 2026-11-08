module

public import IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership
public import IntegerMultBounds.NLogN.PhaseCellHaloLayers

/-! The actual floor-owned rows lie at the required depth in a principal
window. A cyclic chart moves no original matrix or phase-cell boundary. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership
open PhaseCellMatrix PhaseCellDiscreteGeometry
variable {s : ℕ} [NeZero s]

theorem owned_haloLayer (t L k band depth : ℕ) (ha : depth*band ≤ cut s t L k) :
    haloLayer s (cut s t L k-depth*band) (cut s t L (k+1)+depth*band) band depth =
      haloVertices s (cut s t L k) (cut s t L (k+1)) := by
  simp only [haloLayer,Nat.sub_add_cancel ha,Nat.add_sub_cancel]

theorem owned_in_cyclic_layer (t L k band depth : ℕ)
    (hfit : rows s t L k+2*(depth*band) ≤ s) :
    haloVertices s (cut s t L k) (cut s t L (k+1)) ⊆
      cyclicHaloLayer ((cut s t L k : ZMod s)-(depth*band : ℕ)) 0
        (rows s t L k+2*(depth*band)) band depth := by
  intro i hi
  obtain ⟨hstart,hstop⟩ := (mem_haloVertices _ _ i).mp hi
  let offset := i.val-cut s t L k
  have hoff : offset < rows s t L k := by dsimp only [offset,rows]; omega
  have he : i-((cut s t L k : ZMod s)-(depth*band : ℕ)) =
      ((offset+depth*band : ℕ) : ZMod s) := by
    have hv : i = (i.val : ZMod s) := by simp
    have hc : ((i.val-cut s t L k : ℕ) : ZMod s) =
        (i.val : ZMod s)-(cut s t L k : ZMod s) := Nat.cast_sub hstart
    rw [hv]
    simp only [offset,Nat.cast_add,hc]
    ring
  have hlt : offset+depth*band < s := by omega
  rw [mem_cyclicHaloLayer,he]
  apply (mem_haloVertices _ _ _).mpr
  rw [ZMod.val_cast_of_lt hlt]
  constructor <;> omega

end IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership
