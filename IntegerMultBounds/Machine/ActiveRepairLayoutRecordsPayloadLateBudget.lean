import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsPayloadLateRun

/-! The actual original-input later payload, full-width repair, cleanup and
copy-back retain the certified payload width exponent with all joins paid. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsPayloadLateBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairLayoutRecordsPayloadLateRun
open ActivePrefixDirtyControlConjugationData (FullArray)
open Networks
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

theorem real_cost_absorb (C R V E P : ℝ) (_hR : 0≤R) (hV : 1≤V) (hE : 1≤E)
    (hP : P≤C*V*E) :
    P+1+R*V+1+(5*V+10)≤(C+R+17)*V*E := by
  have hm : (R+17)*V≤(R+17)*V*E := by nlinarith only [mul_nonneg (mul_nonneg (by linarith : 0≤R+17) (by linarith : 0≤V)) (by linarith : 0≤E-1)]
  nlinarith only [hP,hm,hV]

theorem uniform_bound (D : ℕ) : ∃ C : ℝ, 0<C ∧ ∀ (s : Shape) (p : Parameters s) (offset rows : ℕ)
    (_hfit : offset+p.f*p.q≤p.after) (_hn : 0<p.n) (_hb : 2≤p.b) (d : Inputs s p offset rows),
    (cost _hfit _hn _hb d D : ℝ)≤C*(rows*s.recordWidth : ℕ)*
      ((max 1 (p.n*p.b) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau := by
  obtain ⟨C,hC,hbound⟩ := ActivePrefixDirtyControlSequenceOriginalBudget.uniform_bound
  refine ⟨C+(repairConstant D : ℝ)+17,by positivity,?_⟩
  intro s p offset rows _hfit _hn _hb d
  have hP := hbound s p offset rows _hfit _hn _hb d
  have hV : (1:ℝ)≤(rows*s.recordWidth : ℕ) := by
    have hp : 0<s.payload := by have := d.hrecord; omega
    have hr := d.hr
    have hh : 0<rows*s.recordWidth := by unfold Shape.recordWidth; positivity
    exact_mod_cast hh
  have hE : (1:ℝ)≤((max 1 (p.n*p.b) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau :=
    Real.one_le_rpow (by exact_mod_cast le_max_left 1 (p.n*p.b)) Shared50RecursiveBudgetBound.exponent_range.1.le
  have hh := real_cost_absorb C (repairConstant D) ((rows*s.recordWidth:ℕ):ℝ)
    (((max 1 (p.n*p.b) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau)
    (ActivePrefixDirtyControlSequenceOriginalRun.cost _hfit _hn _hb d) (by positivity) hV hE hP
  change ((ActivePrefixDirtyControlSequenceOriginalRun.cost _hfit _hn _hb d+1+
    repairConstant D*(rows*s.recordWidth)+1+(5*(rows*s.recordWidth)+10):ℕ):ℝ)≤_
  push_cast at hh ⊢
  exact hh

theorem certified_runs (D : ℕ) : ∃ C : ℝ, 0<C ∧ ∀ (s : Shape) (p : Parameters s) (offset rows : ℕ)
    (_hfit : offset+p.f*p.q≤p.after) (_hn : 0<p.n) (_hb : 2≤p.b) (d : Inputs s p offset rows)
    (x : FullArray s rows) (_hq3 : p.b+3≤p.q)
    (_hR : (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair d).geom.addressBits+1≤s.payload)
    (_hdensity : VaryingControlRepairDensity.lateDensity p.q p.b p.n*
      ((ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair d).geom.addressBits+1)≤D),
    ∃ B : ℕ, HoareTime ActiveRepairLayoutRecordsPayloadLateRun.program (fun v => v=ActiveRepairLayoutRecordsPayloadLateRun.input d x) (fun v => v=ActiveRepairLayoutRecordsPayloadLateRun.output d x) B ∧
      (B:ℝ)≤C*(rows*s.recordWidth : ℕ)*
        ((max 1 (p.n*p.b) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau := by
  obtain ⟨C,hC,hbound⟩ := uniform_bound D
  refine ⟨C,hC,?_⟩
  intro s p offset rows _hfit _hn _hb d x _hq3 _hR _hdensity
  exact ⟨cost _hfit _hn _hb d D,runs _hfit _hn _hb d x _hq3 _hR D _hdensity,hbound s p offset rows _hfit _hn _hb d⟩

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsPayloadLateBudget
