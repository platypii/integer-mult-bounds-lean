module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGridDispatch
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedFullLineScalars

/-! The full-period branch is a singleton instance of the selected S3 ledger. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

private theorem singleton_cost_le {α : Type} (cost : α → ℕ) (tape : List α → ℕ) (r : α) :
    cost r ≤ ([r].map (fun r => cost r+3)).sum+6*[r].length+2*tape [r]+10 := by
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
  omega

theorem selectedFullLineGridCost_fast_le (ct : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ (T A : ℕ) (work : Fin 303 → Fin T) (d : ℝ) (u target : ℕ)
        (Fs : List (ZMod (Sizes.s n i) → GaussianInt)),
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      GridDispatchReady (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) d
        (fullLineGridRecord (A := A) (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target (Sizes.t n i) Fs) →
      ((fullLineGridRecord (A := A) (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target (Sizes.t n i) Fs).gridCost
        (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) work : ℝ) ≤
      2624000*(Sizes.T n : ℝ)+(Fs.length : ℝ)*D*(Sizes.t n i : ℝ)*
        (1+(PhaseCellBand.width (Sizes.p n) u : ℝ)^2/Sizes.d n)*(Sizes.p n : ℝ)^(129/128 : ℝ)+410 := by
  obtain ⟨D,hD,hcost⟩ := selectedGridDispatchLedger_fast_le ct
  refine ⟨D,hD,?_⟩
  filter_upwards [hcost] with n hn
  intro h i _ T A work d u target Fs hu htarget hr
  let r := fullLineGridRecord (A := A) (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target (Sizes.t n i) Fs
  let key : SelectedFamilyKey n i ct :=
    (⟨u,by omega⟩,⟨target,by omega⟩,⟨0,by omega⟩,⟨Sizes.s n i,by omega⟩)
  have hm : MatchesSelectedFamilyKey r key := ⟨rfl,rfl,rfl,rfl⟩
  have hb := hn h i T A work d [r] (fun _ => key) (by simp)
    (by intro x hx; have he := List.mem_singleton.mp hx; subst x; exact hm)
    (by intro x hx; have he := List.mem_singleton.mp hx; subst x; exact hr)
  have hl := singleton_cost_le (fun r => FamilyDispatchInput.gridCost (Sizes.p n)
    (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) work r)
    (fun records => (descriptorScheduleTape work FamilyDispatchInput.words records).length) r
  have hlr := Nat.cast_le (α := ℝ).mpr hl
  have hinputs : r.inputs = Fs := rfl
  have huval : r.u = u := rfl
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,hinputs,huval] at hb
  exact hlr.trans (by simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using hb)

theorem selectedFullLineGridStock_scaled_volume_le (ct scale : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ (T Q A : ℕ) (producer : PackedProducerPlan T Q) (d : ℝ) (u target : ℕ)
        (Fs : List (ZMod (Sizes.s n i) → GaussianInt)),
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      GridDispatchReady (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) d
        (fullLineGridRecord (A := A) (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target (Sizes.t n i) Fs) →
      scale*producer.gridStock (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i)
        (fullLineGridRecord (A := A) (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target (Sizes.t n i) Fs) ≤
      1312000*scale*(Fs.length*Sizes.s n i*inverseFullInputWidth (Sizes.p n) u
        (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target (Sizes.s n i) (Sizes.t n i))+Sizes.T n := by
  filter_upwards [selectedGridDispatchStockLedger_scaled_volume_le ct scale] with n hn
  intro h i _ T Q A producer d u target Fs hu htarget hr
  let r := fullLineGridRecord (A := A) (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target (Sizes.t n i) Fs
  let key : SelectedFamilyKey n i ct :=
    (⟨u,by omega⟩,⟨target,by omega⟩,⟨0,by omega⟩,⟨Sizes.s n i,by omega⟩)
  have hm : MatchesSelectedFamilyKey r key := ⟨rfl,rfl,rfl,rfl⟩
  have hb := hn h i T A producer.gridWork d [r] (fun _ => key) (by simp)
    (by intro x hx; have he := List.mem_singleton.mp hx; subst x; exact hm)
    (by intro x hx; have he := List.mem_singleton.mp hx; subst x; exact hr)
  have hinputs : r.inputs = Fs := rfl
  have hwidth : r.width (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) =
      inverseFullInputWidth (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target (Sizes.s n i) (Sizes.t n i) := rfl
  change scale*producer.gridStock (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) r ≤ _
  unfold PackedProducerPlan.gridStock
  simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,hinputs,hwidth] using hb

end IntegerMultBounds.MathlibTM2.Cost
