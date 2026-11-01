module

public import IntegerMultBounds.NLogN.PhaseCellCoreHaloOverlap
public import IntegerMultBounds.NLogN.PhaseCellCoreDescriptors

/-! Sparse phase boundaries are charged by overlap; artificial endpoints by
one short guard per distinct core, independently of the replica count. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix
open Finset PhaseCellDiscreteGeometry
open scoped BigOperators

/-- The boundary band may differ from the guard used to construct core halos.
This permits the doubled stencil band in recovery to use the same schedule. -/
theorem coreHalo_boundary_volume_le {s : ℕ} [NeZero s] (t width band n boundaryBand : ℕ)
    (hw : 0 < width) (hr : n*band ≤ width) :
    (∑ k ∈ (coreIndices s width).toFinset,
      (haloBoundary s t boundaryBand (coreHaloEndpoints s width k band n).1
        (coreHaloEndpoints s width k band n).2).card) ≤
      6*(Finset.univ \ interiorSet s t boundaryBand).card+
        2*boundaryBand*(coreIndices s width).length := by
  let K := (coreIndices s width).toFinset
  let E := Finset.univ \ interiorSet s t boundaryBand
  have hoverlap := coreHalo_inter_volume_le_six width band n hw hr E
  have heq (k : ℕ) :
      haloVertices s (coreHaloEndpoints s width k band n).1
        (coreHaloEndpoints s width k band n).2 \ interiorSet s t boundaryBand =
        coreHalo s width k band n ∩ E := by
    rw [coreHaloEndpoints_set]
    ext i
    simp only [mem_sdiff,mem_inter,mem_univ,true_and,E]
  have hlocal (k : ℕ) :
      (haloBoundary s t boundaryBand (coreHaloEndpoints s width k band n).1
        (coreHaloEndpoints s width k band n).2).card ≤
      (coreHalo s width k band n ∩ E).card+2*boundaryBand := by
    have hh := haloBoundary_card_le s t boundaryBand
      (coreHaloEndpoints s width k band n).1 (coreHaloEndpoints s width k band n).2
    rwa [heq] at hh
  calc
    _ ≤ ∑ k ∈ K, ((coreHalo s width k band n ∩ E).card+2*boundaryBand) :=
      sum_le_sum (fun k _ => hlocal k)
    _ = (∑ k ∈ K, (coreHalo s width k band n ∩ E).card)+
        2*boundaryBand*(coreIndices s width).length := by
      rw [sum_add_distrib]
      simp only [sum_const,nsmul_eq_mul,Nat.cast_id,K,
        List.toFinset_card_of_nodup (coreIndices_nodup s width)]
      ring
    _ ≤ _ := Nat.add_le_add_right hoverlap _

end IntegerMultBounds.NLogN.PhaseCellMatrix
