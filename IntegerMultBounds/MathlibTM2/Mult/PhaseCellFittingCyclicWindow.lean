module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedWindows
public import IntegerMultBounds.NLogN.PhaseCellCyclicPrincipalGeometry
public import IntegerMultBounds.NLogN.PhaseCellCoreGather

/-! Fitting core-gather geometry identifies the executed cyclic principal
window with the locality interface's generated halo. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
open IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem coreGather_cyclicWindow_eq {s : ℕ} [NeZero s] (width p u target L k : ℕ)
    (hk : k ∈ coreGatherIndices s width (localityDepth p target*PhaseCellBand.width p u) L) :
    cyclicPrincipalVertices s (coreStart width k-localityDepth p target*PhaseCellBand.width p u) L =
      (generatedWindow s width p u target k).halo := by
  obtain ⟨hleft,hright,hlen⟩ := coreGatherIndices_spec _ _ _ _ k hk
  have hfit : coreStart width k-localityDepth p target*PhaseCellBand.width p u+L ≤ s := by omega
  have hmin : min L (s-(coreStart width k-localityDepth p target*PhaseCellBand.width p u)) = L := by omega
  have hend : coreStart width k-localityDepth p target*PhaseCellBand.width p u+L =
      coreStart width k+coreLength s width k+localityDepth p target*PhaseCellBand.width p u := by omega
  change cyclicPrincipalVertices s _ L = coreHalo s width k _ _
  rw [coreHalo,if_pos ⟨hleft,hright⟩]
  simp only [cyclicPrincipalVertices,hmin,Nat.sub_self,hend]
  simp [haloVertices]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
