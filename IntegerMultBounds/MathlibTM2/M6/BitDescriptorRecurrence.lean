module

public import IntegerMultBounds.MathlibTM2.M6.BitNodeCost
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodChildLayout

/-! The five-class recurrence on role streams with rank-sized active fields. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode

open IntegerMultBounds.Machine.RecursiveInterchangeLayout
open IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.MathlibTM2.Layer.SelectedMoments

/-- For a physical realization with the scheduled rank descriptors, row splitting
supplies the recurrence weights and the active field supplies its size argument.
The local cost is measured per unit of parent volume. -/
theorem five_descriptor_closed {Node : Type*} (q : ℕ) (layout : Node → Descriptor)
    (child : Node → Fin nodeChildren5.length → Node) (cost : Node → ℝ) (u : ℕ)
    {τ lam K C₀ C₁ : ℝ}
    (hτ : 0 ≤ τ) (hτl : τ ≤ lam) (hlam : 1 - bitSaving < lam) (hK : 1 ≤ K)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hu : 1 ≤ u)
    (hleaf : ∀ x, (layout x).width ≤ u → cost x ≤ C₀ * (layout x).width)
    (physical : ∀ x, u < (layout x).width →
      ∃ b, (layout x).width = 64*b ∧ 142080 ∣ (layout x).rows ∧
        0 < volume q (layout x) ∧ ∀ i, layout (child x i) =
          rankDescriptor q (nodeChildren5[i.val]*b) ((64-nodeChildren5[i.val])*b)
            (role (layout x) 142080))
    (hcost : ∀ x, u < (layout x).width →
      cost x ≤ C₁ * ((K * (layout x).width) ^ τ + 1) +
        ∑ i, ((volume q (layout (child x i)) : ℝ) / volume q (layout x)) * cost (child x i)) :
    ∀ x, cost x ≤
      2 * C₁ / (1 - ((42 : ℝ) / 64) ^ (lam - (1 - bitSaving))) * K ^ τ * ((layout x).width : ℝ) ^ lam +
      C₀ * ((layout x).width : ℝ) ^ (1 - bitSaving) * (u : ℝ) ^ (1 - (1 - bitSaving)) := by
  have measures (x) (hx : u < (layout x).width) (i : Fin nodeChildren5.length) :
      (layout (child x i)).width * 64 = nodeChildren5[i.val] * (layout x).width ∧
      volume q (layout (child x i)) * 142080 = volume q (layout x) := by
    obtain ⟨b,width,divides,_,desc⟩ := physical x hx
    rw [desc i]
    exact rankDescriptor_role_size (M := q) _ _ _ b width
      ((nodeChildren5_le i).trans (by decide : 42 ≤ 64)) divides
  apply five_variable_closed (fun x => (layout x).width) child cost u hτ hτl hlam hK hC₀ hC₁ hu hleaf
  · intro x hx i
    have width : ((layout (child x i)).width : ℝ)*64 = nodeChildren5[i.val]*(layout x).width := by
      exact_mod_cast (measures x hx i).1
    linarith
  · intro x hx
    have weight (i : Fin nodeChildren5.length) :
        (volume q (layout (child x i)) : ℝ) / volume q (layout x) = 1/142080 := by
      obtain ⟨_,_,_,pos,_⟩ := physical x hx
      have nonzero : (volume q (layout x) : ℝ) ≠ 0 := by exact_mod_cast pos.ne'
      apply (div_eq_div_iff nonzero (by norm_num)).2
      simpa using (show (volume q (layout (child x i)) : ℝ)*142080 = volume q (layout x) by
        exact_mod_cast (measures x hx i).2)
    simpa only [weight] using hcost x hx

end IntegerMultBounds.MathlibTM2.M6.BitNode
