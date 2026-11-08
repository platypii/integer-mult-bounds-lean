module

public import IntegerMultBounds.MathlibTM2.Routing.HaloAxisCoordinates
public import IntegerMultBounds.MathlibTM2.Routing.RetainedHaloTensor

/-! The logical output of the verified axis program extends a retained-halo
tensor invariant by one axis, leaving all previous projections in place. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloAxisTensorInvariant
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Routing
  HaloPassContext RectangularHaloCoordinates RetainedHaloTensor
variable {ι : Type} [DecidableEq ι]

def axisOf (p : Parameters) : Axis := ⟨p.N,p.L,p.H,p.N_pos,p.L_pos⟩

theorem transform_pullback (p : Parameters) (axis : ι → Axis) (retained : Finset ι) (i : ι)
    (hi : i ∉ retained) (haxis : axis i = axisOf p)
    (f : (ι → ℕ) → GaussianInt) (base : ℕ → ℕ → ι → ℕ × ℕ)
    (fibers : List (List (List (List GaussianInt)))) (hshape : ∀ matrices ∈ fibers, Shape p matrices)
    (hinv : ∀ a < fibers.length, ∀ k < p.N, ∀ b < p.B, ∀ t < p.L,
      entry4 (0 : GaussianInt) fibers a k b t =
        pullback axis retained f (Function.update (base a b) i (k,t))) :
    ∀ a < fibers.length, ∀ k < p.N, ∀ b < p.B, ∀ t < p.L+2*p.H,
      entry4 (0 : GaussianInt) (HaloAxisCoordinates.transform p fibers) a k b t =
        pullback axis (insert i retained) f (Function.update (base a b) i (k,t)) := by
  intro a ha k hk b hb t ht
  rw [HaloAxisCoordinates.transform_entry p fibers hshape a k b t ha hk hb ht]
  have hp := sourcePair_bounds (axis i) (k,t)
  have hcoarse : sourceIndex p.N p.L p.H k t/p.L < p.N := by
    simpa only [sourcePair,haxis,axisOf] using hp.1
  have hlocal : sourceIndex p.N p.L p.H k t%p.L < p.L := by
    simpa only [sourcePair,haxis,axisOf] using hp.2
  rw [hinv a ha _ hcoarse b hb _ hlocal,pullback_insert axis retained i hi,
    updateAxis_update]
  simp only [sourcePair,haxis,axisOf]

end IntegerMultBounds.MathlibTM2.Routing.HaloAxisTensorInvariant
