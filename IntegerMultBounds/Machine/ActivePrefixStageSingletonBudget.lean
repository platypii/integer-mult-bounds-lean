import IntegerMultBounds.Machine.ActivePrefixStageSingletonRun
import IntegerMultBounds.Machine.ActiveTargetHighestLayoutOriginalBudget

/-! Both singleton source orders have uniform linear cost in the complete
current array volume. Producer synthesis, highest-bit action and all consumer
word erasure are included; no packed-repair density hypothesis is needed. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageSingletonBudget
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters ActivePrefixStageGeometry
open ActivePrefixStageSingletonData ActivePrefixStageSingletonRun

 theorem uniform_bound : ∃ C : ℝ,0<C ∧
    (∀ {s : Shape} (d : Inputs s) (horder : d.stage.source.val<d.stage.target.val),
      (earlyCost d horder:ℝ)≤C*((d.rows*s.recordWidth:ℕ):ℝ)) ∧
    (∀ {s : Shape} (d : Inputs s) (horder : d.stage.target.val<d.stage.source.val),
      (lateCost d horder:ℝ)≤C*((d.rows*s.recordWidth:ℕ):ℝ)) := by
  obtain ⟨C,hC,hearly,hlate⟩ := ActiveTargetHighestLayoutOriginalBudget.uniform_layout_bound
  refine ⟨C+1005002,by positivity,?_,?_⟩
  · intro s d horder
    have hP := ActivePrefixStageHeadersBudget.uniform_bound .early d.stage d.rows d.hG d.hGK
      horder d.hr d.hrecord
    have hE := ActivePrefixStageFullErase.bound .early d.toInputs horder
    have hP' : (ActivePrefixStageHeadersPlaced.cost .early d.stage d.rows:ℝ)≤1000000*((d.rows*s.recordWidth:ℕ):ℝ) := by exact_mod_cast hP
    have hE' : (ActivePrefixStageFullErase.cost .early d.toInputs:ℝ)≤5000*((d.rows*s.recordWidth:ℕ):ℝ) := by exact_mod_cast hE
    have hS := hearly s (params d) (earlyOffset d.stage) d.rows (early_fits d.stage horder)
      (early_high_positive d.stage horder) (positive_H d.stage d.hG) d.hr (by have := d.hrecord; omega)
    have hS' : (earlyStageCost d horder:ℝ)≤C*((d.rows*s.recordWidth:ℕ):ℝ) := by
      simpa only [earlyStageCost,Nat.cast_mul] using hS
    have hV : (1:ℝ)≤((d.rows*s.recordWidth:ℕ):ℝ) := by
      have hp : 0<s.payload := by have := d.hrecord; omega
      have hv : 0<d.rows*s.recordWidth := Nat.mul_pos d.hr (by unfold Shape.recordWidth; positivity)
      exact_mod_cast hv
    unfold earlyCost
    push_cast at hP' hE' hS' hV ⊢
    nlinarith only [hP',hE',hS',hV]
  · intro s d horder
    have hP := ActivePrefixStageHeadersBudget.uniform_bound .late d.stage d.rows d.hG d.hGK
      horder d.hr d.hrecord
    have hE := ActivePrefixStageFullErase.bound .late d.toInputs horder
    have hP' : (ActivePrefixStageHeadersPlaced.cost .late d.stage d.rows:ℝ)≤1000000*((d.rows*s.recordWidth:ℕ):ℝ) := by exact_mod_cast hP
    have hE' : (ActivePrefixStageFullErase.cost .late d.toInputs:ℝ)≤5000*((d.rows*s.recordWidth:ℕ):ℝ) := by exact_mod_cast hE
    have hS := hlate s (params d) (lateOffset d.stage) d.rows (late_fits d.stage horder)
      (positive_before d.stage) (positive_H d.stage d.hG) d.hr (by have := d.hrecord; omega)
    have hS' : (lateStageCost d horder:ℝ)≤C*((d.rows*s.recordWidth:ℕ):ℝ) := by
      simpa only [lateStageCost,Nat.cast_mul] using hS
    have hV : (1:ℝ)≤((d.rows*s.recordWidth:ℕ):ℝ) := by
      have hp : 0<s.payload := by have := d.hrecord; omega
      have hv : 0<d.rows*s.recordWidth := Nat.mul_pos d.hr (by unfold Shape.recordWidth; positivity)
      exact_mod_cast hv
    unfold lateCost
    push_cast at hP' hE' hS' hV ⊢
    nlinarith only [hP',hE',hS',hV]

end IntegerMultBounds.Machine.ActivePrefixStageSingletonBudget
