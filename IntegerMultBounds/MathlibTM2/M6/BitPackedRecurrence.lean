module

public import IntegerMultBounds.MathlibTM2.M6.BitDescriptorRecurrence
public import IntegerMultBounds.MathlibTM2.Cover.FallbackWeightedLeafBudget

/-! PR589 root cost with the stopped packed coordinate budget at each leaf. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine.RecursiveInterchangeLayout
open IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.MathlibTM2.Layer.SelectedMoments
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

theorem five_packed_root_closed [M8.Machine.Net] {Node : Type*} (layout : Node → Descriptor)
    (child : Node → Fin nodeChildren5.length → Node) (steps : Node → ℕ)
    (root : Node) (depth u tapes push entryTapes returnTapes : ℕ) {τ lam K C₁ : ℝ}
    (hτ : 0 ≤ τ) (hτl : τ ≤ lam) (hlam : 1 - bitSaving < lam) (hK : 1 ≤ K)
    (hC₁ : 0 ≤ C₁) (hu : 1 ≤ u)
    (width : 64^depth ∣ (layout root).width) (rows : 142080^depth ∣ (layout root).rows)
    (stop : (layout root).width * 42^depth ≤ u * 64^depth)
    (positive : 0 < volume prime (layout root))
    (hleaf : ∀ x, 0 < volume prime (layout x) → (layout x).width ≤ u →
      ∃ d w, 0 < d ∧ d ≤ 42 ∧ (layout x).width = d*(w+1) ∧
        steps x ≤ packedCoordinatesTime d (volume prime (layout x)) w tapes push entryTapes returnTapes)
    (physical : ∀ x, u < (layout x).width → 0 < volume prime (layout x) →
      64 ∣ (layout x).width → 142080 ∣ (layout x).rows → ∀ i, layout (child x i) = scheduledChild prime (layout x) i)
    (hcost : ∀ x, u < (layout x).width → 0 < volume prime (layout x) →
      64 ∣ (layout x).width → 142080 ∣ (layout x).rows →
      (steps x : ℝ) ≤ C₁ * ((K * (layout x).width) ^ τ + 1) * volume prime (layout x) +
        ((∑ i, steps (child x i) : ℕ) : ℝ)) :
    (steps root : ℝ) ≤
      (2 * C₁ / (1 - ((42 : ℝ) / 64) ^ (lam - (1 - bitSaving))) * K ^ τ * ((layout root).width : ℝ) ^ lam +
      packedCoordinatesRate 42 tapes push entryTapes returnTapes * ((layout root).width : ℝ) ^ (1 - bitSaving) * (u : ℝ) ^ (1 - (1 - bitSaving))) * volume prime (layout root) := by
  apply five_root_closed prime layout child steps root depth u hτ hτl hlam hK _ hC₁ hu width rows stop
    positive _ physical hcost
  · unfold packedCoordinatesRate weightedLeafRate
    positivity
  · intro x pos small
    obtain ⟨d,w,active,rankBound,split,run⟩ := hleaf x pos small
    exact packedCoordinates_steps_linear _ (M8.RevMachine.LeafCore.positive_of_volume pos)
      d 42 w tapes push entryTapes returnTapes _ active rankBound split run

end IntegerMultBounds.MathlibTM2.M6.BitNode
