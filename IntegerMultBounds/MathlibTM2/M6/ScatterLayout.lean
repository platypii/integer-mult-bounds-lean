module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic

/-! A fixed register layout commutes with a scalar stream map exactly when
its nonzero coefficients connect registers with the same layout. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6

open Matrix

theorem scalar_layout_iff {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq Ω]
    (M : Matrix ι ι (ZMod 2)) (layout : ι → Ω → Ω) :
    (∀ (bank : Ω → ι → ZMod 2) x i,
      (M *ᵥ (fun j => bank (layout j x) j)) i = (M *ᵥ bank (layout i x)) i) ↔
    ∀ i j, M i j ≠ 0 → layout i = layout j := by
  constructor
  · intro comm i j nz
    funext x
    by_contra ne
    let bank := fun (y : Ω) (k : ι) => if k = j ∧ y = layout j x then (1 : ZMod 2) else 0
    have h := comm bank x i
    simp only [Matrix.mulVec, dotProduct, bank] at h
    have entry (k : ι) : (k = j ∧ layout k x = layout j x) ↔ k = j :=
      ⟨And.left, fun eq => ⟨eq, congrArg (fun l => layout l x) eq⟩⟩
    simp [entry, ne, mul_ite] at h
    exact nz h
  · intro closed bank x i
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : M i j = 0
    · simp [h]
    · rw [closed i j h]

end IntegerMultBounds.MathlibTM2.M6
