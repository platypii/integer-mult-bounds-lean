import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullLateRun
import IntegerMultBounds.Machine.ActiveTargetHighestLayoutOriginalBudget

/-! Complete physical later low/high action retains the certified compact
width exponent, paying original highest geometry synthesis and all cleanup. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullLateBudget
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairLayoutRecordsFullLateRun

theorem uniform_bound (D : ℕ) : ∃ C : ℝ,0<C ∧
    ∀ (s : Shape) (p : Parameters s) (offset rows : ℕ)
      (hfit : offset+p.f*p.q≤p.after) (hn : 0<p.n) (hb : 2≤p.b)
      (d : Inputs s p offset rows) (hbefore : 1≤p.before) (hH : 1≤s.H),
      (cost D hfit hn hb d hbefore hH : ℝ)≤
        C*(rows*s.recordWidth : ℕ)*((max 1 (p.n*p.b) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau := by
  obtain ⟨L,hL,low⟩ := ActiveRepairLayoutRecordsPayloadLateBudget.uniform_bound D
  obtain ⟨H,hHbound,_,high⟩ := ActiveTargetHighestLayoutOriginalBudget.uniform_layout_bound
  refine ⟨L+H+1,by positivity,?_⟩
  intro s p offset rows hfit hn hb d hbefore hH
  have hp : 0<s.payload := by have := d.hrecord; omega
  have hl := low s p offset rows hfit hn hb d
  have hh := high s p offset rows hfit hbefore hH d.hr hp
  have hv : (1 : ℝ)≤(rows*s.recordWidth : ℕ) := by
    have hr := d.hr
    have h : 0<rows*s.recordWidth := by unfold Shape.recordWidth; positivity
    exact_mod_cast h
  have he : (1 : ℝ)≤((max 1 (p.n*p.b) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau :=
    Real.one_le_rpow (by exact_mod_cast le_max_left 1 (p.n*p.b))
      Shared50RecursiveBudgetBound.exponent_range.1.le
  have hm := mul_le_mul_of_nonneg_left he (show (0 : ℝ)≤(rows*s.recordWidth : ℕ) by positivity)
  have hhigh := mul_le_mul_of_nonneg_left hm hHbound.le
  change ((ActiveRepairLayoutRecordsPayloadLateRun.cost hfit hn hb d D+
    highCost s p offset rows hfit hbefore hH d.hr hp+1 : ℕ) : ℝ)≤_
  unfold highCost
  push_cast at hl hh hv hm hhigh ⊢
  nlinarith only [hl,hh,hv,hm,hhigh]

end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullLateBudget
