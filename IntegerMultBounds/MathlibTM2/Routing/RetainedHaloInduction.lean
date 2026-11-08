module

public import IntegerMultBounds.MathlibTM2.Routing.RetainedHaloTensor
import Mathlib.Data.List.Nodup

/-! Induction over distinct retained axes. The coordinate operation is precisely
that realized by the ordered halo pass; validity is transported at every step. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.RetainedHaloInduction
open RetainedHaloTensor
variable {ι E : Type} [DecidableEq ι]

def extendAxes (axis : ι → Axis) : List ι → ((ι → ℕ × ℕ) → E) → (ι → ℕ × ℕ) → E
  | [], g => g
  | i :: axes, g => extendAxes axis axes (fun coords => g (updateAxis axis i coords))

theorem extendAxes_pullback (axis : ι → Axis) (axes : List ι) (retained : Finset ι)
    (hnodup : axes.Nodup) (hfresh : ∀ i ∈ axes, i ∉ retained)
    (f : (ι → ℕ) → E) (g : (ι → ℕ × ℕ) → E)
    (hinv : ∀ coords, Valid axis retained coords → g coords = pullback axis retained f coords) :
    ∀ coords, Valid axis (retained ∪ axes.toFinset) coords →
      extendAxes axis axes g coords = pullback axis (retained ∪ axes.toFinset) f coords := by
  induction axes generalizing retained g with
  | nil => simpa only [List.toFinset_nil,Finset.union_empty,extendAxes] using hinv
  | cons i axes ih =>
    have hi : i ∉ retained := hfresh i (by simp)
    have htail : ∀ j ∈ axes, j ∉ insert i retained := by
      intro j hj
      have hji : j ≠ i := fun he => (List.nodup_cons.mp hnodup).1 (he ▸ hj)
      simp only [Finset.mem_insert,not_or]
      exact ⟨hji,hfresh j (by simp [hj])⟩
    have hstep : ∀ coords, Valid axis (insert i retained) coords →
        g (updateAxis axis i coords) = pullback axis (insert i retained) f coords := by
      intro coords hc
      rw [hinv _ (updateAxis_valid axis retained i hi coords hc),pullback_insert axis retained i hi]
    have hsets : insert i retained ∪ axes.toFinset = retained ∪ (i :: axes).toFinset := by
      ext j
      simp only [Finset.mem_union,Finset.mem_insert,List.toFinset_cons]
      tauto
    intro coords hc
    have hout := ih (insert i retained) (List.nodup_cons.mp hnodup).2 htail
      (fun coords => g (updateAxis axis i coords)) hstep coords
    rw [hsets] at hout
    exact hout hc

end IntegerMultBounds.MathlibTM2.Routing.RetainedHaloInduction
