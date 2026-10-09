import IntegerMultBounds.Machine.ActivePrefixStageFullEarlyRun
import IntegerMultBounds.Machine.ActivePrefixStageFullLateRun

/-! Original-only full selected stages retain the certified compact-width
exponent after paying descriptor synthesis, copying, erasure and both joins. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageFullBudget
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters ActivePrefixStageGeometry
open ActivePrefixStageFullData

 theorem overhead {s : Shape} (order : ActivePrefixStageHeadersData.Order) (d : Inputs s)
    (horder : ActivePrefixStageHeadersSchedule.Ordered order d.stage) :
    ActivePrefixStageHeadersPlaced.cost order d.stage d.rows+ActivePrefixStageFullErase.cost order d+2≤
      1005002*(d.rows*s.recordWidth) := by
  have hp := ActivePrefixStageHeadersBudget.uniform_bound order d.stage d.rows
    d.hG d.hGK horder d.hr d.hrecord
  have he := ActivePrefixStageFullErase.bound order d horder
  have hpay : 0<s.payload := by have := d.hrecord; omega
  have hrecord : 0<s.recordWidth := by unfold Shape.recordWidth; positivity
  have hvolume := Nat.mul_pos d.hr hrecord
  omega

 theorem early_uniform_bound (D : ℕ) : ∃ C : ℝ,0<C ∧
    ∀ (s : Shape) (d : Inputs s) (horder : d.stage.source.val<d.stage.target.val),
      (ActivePrefixStageFullEarlyRun.cost D d horder : ℝ)≤C*(d.rows*s.recordWidth : ℕ)*
        ((max 1 ((d.stage.f-1)*s.guard) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau := by
  obtain ⟨C,hC,hbound⟩ := ActiveRepairLayoutRecordsFullEarlyBudget.uniform_bound D
  refine ⟨C+1005002,by positivity,?_⟩
  intro s d horder
  have hp : 0<s.payload := by have := d.hrecord; omega
  have hh := hbound s (parameters d.stage d.hG d.hGK) (earlyOffset d.stage) d.rows
    (early_fits d.stage horder) (early_high_positive d.stage horder) (positive_H d.stage d.hG) d.hr hp
  have ho := overhead .early d horder
  have hor : ((ActivePrefixStageHeadersPlaced.cost .early d.stage d.rows+ActivePrefixStageFullErase.cost .early d+2 : ℕ) : ℝ)≤
      1005002*(d.rows*s.recordWidth : ℕ) := by exact_mod_cast ho
  have he : (1 : ℝ)≤((max 1 ((d.stage.f-1)*s.guard) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau :=
    Real.one_le_rpow (by exact_mod_cast le_max_left 1 ((d.stage.f-1)*s.guard))
      Shared50RecursiveBudgetBound.exponent_range.1.le
  have hm := mul_le_mul_of_nonneg_left he (show (0 : ℝ)≤1005002*(d.rows*s.recordWidth : ℕ) by positivity)
  change (ActivePrefixStageFullEarlyRun.stageCost D d horder : ℝ)≤C*(d.rows*s.recordWidth : ℕ)*
    ((max 1 ((d.stage.f-1)*s.guard) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau at hh
  unfold ActivePrefixStageFullEarlyRun.cost
  push_cast at hh hor hm ⊢
  nlinarith only [hh,hor,hm]

 theorem late_uniform_bound (D : ℕ) : ∃ C : ℝ,0<C ∧
    ∀ (s : Shape) (d : Inputs s) (horder : d.stage.target.val<d.stage.source.val)
      (hn : 0<d.stage.f-1) (hb : 2≤s.guard),
      (ActivePrefixStageFullLateRun.cost D d horder hn hb : ℝ)≤C*(d.rows*s.recordWidth : ℕ)*
        ((max 1 ((d.stage.f-1)*s.guard) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau := by
  obtain ⟨C,hC,hbound⟩ := ActiveRepairLayoutRecordsFullLateBudget.uniform_bound D
  refine ⟨C+1005002,by positivity,?_⟩
  intro s d horder hn hb
  have hh := hbound s (parameters d.stage d.hG d.hGK) (lateOffset d.stage) d.rows
    (late_fits d.stage horder) hn hb (descriptors .late d) (positive_before d.stage) (positive_H d.stage d.hG)
  have ho := overhead .late d horder
  have hor : ((ActivePrefixStageHeadersPlaced.cost .late d.stage d.rows+ActivePrefixStageFullErase.cost .late d+2 : ℕ) : ℝ)≤
      1005002*(d.rows*s.recordWidth : ℕ) := by exact_mod_cast ho
  have he : (1 : ℝ)≤((max 1 ((d.stage.f-1)*s.guard) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau :=
    Real.one_le_rpow (by exact_mod_cast le_max_left 1 ((d.stage.f-1)*s.guard))
      Shared50RecursiveBudgetBound.exponent_range.1.le
  have hm := mul_le_mul_of_nonneg_left he (show (0 : ℝ)≤1005002*(d.rows*s.recordWidth : ℕ) by positivity)
  change (ActivePrefixStageFullLateRun.stageCost D d horder hn hb : ℝ)≤C*(d.rows*s.recordWidth : ℕ)*
    ((max 1 ((d.stage.f-1)*s.guard) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau at hh
  unfold ActivePrefixStageFullLateRun.cost
  push_cast at hh hor hm ⊢
  nlinarith only [hh,hor,hm]

end IntegerMultBounds.Machine.ActivePrefixStageFullBudget
