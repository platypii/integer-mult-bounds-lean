import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullEarlyRun
import IntegerMultBounds.Machine.ActiveTargetHighestLayoutOriginalBudget

/-! Complete physical early low/high action retains the certified compact
width exponent while paying original highest geometry synthesis and cleanup. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullEarlyBudget
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes (Parameters)
open ActiveTargetHighestPairLayoutGeometry (sourceHigh)
open ActiveRepairLayoutRecordsFullEarlyRun

theorem uniform_bound (D : ℕ) : ∃ C : ℝ,0<C ∧
    ∀ (s : Shape) (p : Parameters s) (offset rows : ℕ)
      (hfit : offset+p.f*p.q≤p.before) (hsource : 0<sourceHigh s p offset)
      (hH : 1≤s.H) (hr : 0<rows) (hp : 0<s.payload),
      (cost D s p offset rows hfit hsource hH hr hp : ℝ)≤
        C*(rows*s.recordWidth : ℕ)*((max 1 (p.n*p.b) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau := by
  obtain ⟨L,hL,low⟩ := ActiveRepairLayoutRecordsPayloadEarlyClean.uniform_bound D
  obtain ⟨H,hHbound,high,_⟩ := ActiveTargetHighestLayoutOriginalBudget.uniform_layout_bound
  refine ⟨L+H+1,by positivity,?_⟩
  intro s p offset rows hfit hsource hH hr hp
  have hl := low s p rows hr hp
  have hh := high s p offset rows hfit hsource hH hr hp
  have hv : (1 : ℝ)≤(rows*s.recordWidth : ℕ) := by
    have h : 0<rows*s.recordWidth := by unfold Shape.recordWidth; positivity
    exact_mod_cast h
  have he : (1 : ℝ)≤((max 1 (p.n*p.b) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau :=
    Real.one_le_rpow (by exact_mod_cast le_max_left 1 (p.n*p.b))
      Shared50RecursiveBudgetBound.exponent_range.1.le
  have hm := mul_le_mul_of_nonneg_left he (show (0 : ℝ)≤(rows*s.recordWidth : ℕ) by positivity)
  have hhigh := mul_le_mul_of_nonneg_left hm hHbound.le
  unfold cost highCost
  push_cast at hl hh hv hm hhigh ⊢
  nlinarith only [hl,hh,hv,hm,hhigh]

end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullEarlyBudget
