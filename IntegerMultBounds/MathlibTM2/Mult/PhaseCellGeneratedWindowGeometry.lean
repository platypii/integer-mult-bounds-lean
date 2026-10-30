module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedWindows
public import IntegerMultBounds.NLogN.PhaseCellCoreSetupGroups

/-! Generated regular groups discharge the packed executor's crop geometry. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
open IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {s : ℕ} [NeZero s]

/-- Every non-full endpoint group supplies the exact crop geometry required
by the packed job executor, and its interval is the locality halo. -/
theorem generatedWindow_interval_geometry (width p u target k : ℕ)
    (hne : coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p target) ≠ (0,s)) :
    let radius := localityDepth p target*PhaseCellBand.width p u
    let endpoints := coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p target)
    endpoints.1 = coreStart width k-radius ∧
    endpoints.2 = coreStart width k+coreLength s width k+radius ∧
    radius ≤ coreStart width k ∧
    coreStart width k+coreLength s width k+radius ≤ s ∧
    haloVertices s endpoints.1 endpoints.2 = (generatedWindow s width p u target k).halo := by
  have hfit := coreHaloEndpoints_fits_of_ne_full s width k (PhaseCellBand.width p u)
    (localityDepth p target) hne
  refine ⟨?_,?_,hfit.1,hfit.2,?_⟩
  · simp only [coreHaloEndpoints,if_pos hfit]
  · simp only [coreHaloEndpoints,if_pos hfit]
  · exact coreHaloEndpoints_set width k (PhaseCellBand.width p u) (localityDepth p target)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
