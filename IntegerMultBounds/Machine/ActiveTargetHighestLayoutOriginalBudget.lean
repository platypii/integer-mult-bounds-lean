import IntegerMultBounds.Machine.ActiveTargetHighestLayoutOriginalRun
import IntegerMultBounds.Machine.ActiveTargetHighestLayoutHeadersBudget
import IntegerMultBounds.Machine.ActiveTargetHighestPairOriginalBudget
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsHeadersAfterBudget
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsHeadersBudget

/-! Both layers of highest-bit metadata synthesis, the literal payload action
and all cleanup preserve a uniform linear bound in a containing array volume. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestLayoutOriginalBudget
open ActiveTargetHighestPairData ActiveTargetHighestLayoutOriginalRun
open ActivePrefixLayoutHeadersData (Inputs originalValues)

theorem uniform_bound : ∃ C : ℝ,0<C ∧ ∀ (d : Inputs) (g : Geometry),
    (∀ i,originalValues d i≤volume g) →
    (earlierCost d g : ℝ)≤C*volume g ∧ (laterCost d g : ℝ)≤C*volume g := by
  obtain ⟨C,hC,hbound⟩ := ActiveTargetHighestPairOriginalBudget.uniform_bound
  let H := ActiveTargetHighestLayoutHeadersBudget.constant
  let E := ActiveTargetHighestLayoutHeadersBudget.cleanupConstant
  refine ⟨C+H+E+2,by positivity,?_⟩
  intro d g ho
  have hm := hbound g
  have hV := ActiveTargetHighestPairHeadersBudget.volume_positive g
  have h₀ : (ActiveTargetHighestLayoutHeadersRun.cost .early d : ℝ)≤H*volume g := by
    exact_mod_cast ActiveTargetHighestLayoutHeadersBudget.cost_bound .early d (volume g) hV ho
  have h₁ : (ActiveTargetHighestLayoutHeadersRun.cost .late d : ℝ)≤H*volume g := by
    exact_mod_cast ActiveTargetHighestLayoutHeadersBudget.cost_bound .late d (volume g) hV ho
  have e₀ : (ActiveTargetHighestLayoutHeadersRun.cleanupCost .early d : ℝ)≤E*volume g := by
    exact_mod_cast ActiveTargetHighestLayoutHeadersBudget.cleanup_bound .early d (volume g) hV ho
  have e₁ : (ActiveTargetHighestLayoutHeadersRun.cleanupCost .late d : ℝ)≤E*volume g := by
    exact_mod_cast ActiveTargetHighestLayoutHeadersBudget.cleanup_bound .late d (volume g) hV ho
  have hreal : (1 : ℝ)≤volume g := by exact_mod_cast hV
  unfold earlierCost laterCost cost
  push_cast
  constructor <;> nlinarith [hm.1,hm.2]

open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes (Parameters)
open ActiveTargetHighestPairLayoutGeometry
open ActivePrefixLayoutHeadersGeometry (inputs)

theorem uniform_layout_bound : ∃ C : ℝ,0<C ∧
    (∀ (s : Shape) (p : Parameters s) (offset rows : ℕ)
      (hfit : offset+p.f*p.q≤p.before) (hsource : 0<sourceHigh s p offset)
      (hH : 1≤s.H) (hr : 0<rows) (hp : 0<s.payload),
      (earlierCost (inputs s p offset rows) (early s p offset rows hfit hsource hH hr hp) : ℝ)
        ≤C*(rows*s.recordWidth)) ∧
    (∀ (s : Shape) (p : Parameters s) (offset rows : ℕ)
      (hfit : offset+p.f*p.q≤p.after) (hbefore : 1≤p.before)
      (hH : 1≤s.H) (hr : 0<rows) (hp : 0<s.payload),
      (laterCost (inputs s p offset rows) (late s p offset rows hfit hbefore hH hr hp) : ℝ)
        ≤C*(rows*s.recordWidth)) := by
  obtain ⟨C,hC,hbound⟩ := uniform_bound
  refine ⟨C,hC,?_,?_⟩
  · intro s p offset rows hfit hsource hH hr hp
    have ho : ∀ i,originalValues (inputs s p offset rows) i≤
        volume (early s p offset rows hfit hsource hH hr hp) := by
      rw [early_volume]
      exact ActiveRepairLayoutRecordsHeadersBudget.geometry_bounds hr hp hfit
    have h := (hbound _ _ ho).1
    rwa [early_volume,Nat.cast_mul] at h
  · intro s p offset rows hfit hbefore hH hr hp
    have ho : ∀ i,originalValues (inputs s p offset rows) i≤
        volume (late s p offset rows hfit hbefore hH hr hp) := by
      rw [late_volume]
      exact ActiveRepairLayoutRecordsHeadersAfterBudget.geometry_bounds hr hp hfit
    have h := (hbound _ _ ho).2
    rwa [late_volume,Nat.cast_mul] at h

end IntegerMultBounds.Machine.ActiveTargetHighestLayoutOriginalBudget
