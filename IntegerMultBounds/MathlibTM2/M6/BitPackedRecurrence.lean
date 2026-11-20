module

public import IntegerMultBounds.MathlibTM2.M6.BitDescriptorRecurrence
public import IntegerMultBounds.MathlibTM2.Cover.FallbackCoordinateFrame

/-! PR589 root cost with the stopped packed coordinate budget at each leaf. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine.RecursiveInterchangeLayout
open IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.MathlibTM2.Layer.SelectedMoments
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

private theorem scheduledRank_pos (i : Fin nodeChildren5.length) : 0 < nodeChildren5[i.val] := by
  have mem := nodeChildren5_realizes.mem_iff.mp (List.getElem_mem i.isLt)
  simp only [expand, fiveHistogram, bitHistogram, List.map_cons, List.map_nil, List.flatMap_cons,
    List.flatMap_nil, List.mem_append, List.mem_replicate, List.not_mem_nil, or_false] at mem
  omega

open IntegerMultBounds.Machine M8.RevMachine in
/-- Run the packed loop on a stopped five-class child using the parent atom
width and the rank at the selected occurrence. -/
theorem scheduledPacked_exec [M8.Machine.Net] {T work Q : ℕ} {F U : Type}
    (v : Descriptor) (positive : 0 < volume prime v) (w : ℕ) (width : v.width = 64*(w+1))
    (rows : 142080 ∣ v.rows) (i : Fin nodeChildren5.length)
    (parent parentInv : Fin 64 → ZMod (prime^(w+1))) (reciprocal : ∀ j, parent j * parentInv j = 1)
    (pivot : Fin nodeChildren5[i.val] → ZMod (prime^(w+1))) (unit : ∀ j, IsUnit (pivot j))
    (io : Fin T) (roles : Tapes T prime) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (node scalar : Tapes 1 prime) (arity : ℕ) (st : Tapes 2 prime) (free : Family.NodeFree node)
    (fits : LeafCore.small ≤ work) (cap : (LeafCore.core io).states ≤ Q) :
    PackedCoordinateRun (F := F) (U := U) (scheduledChild prime v i) w
      ((nodeChildren5_le i).trans (by decide : 42 ≤ 64)) parent parentInv pivot io roles f p
      node scalar arity st fits cap := by
  have measures := rankDescriptor_role_size (M := prime) v 142080 64 (w+1) width
    ((nodeChildren5_le i).trans (by decide : 42 ≤ 64)) rows
  have atom : v.width / 64 = w+1 := by simp [width]
  simp only [scheduledChild,atom]
  exact packedCoordinates_exec _ (LeafCore.positive_of_volume
    (Nat.pos_of_mul_pos_right (measures.2.symm ▸ positive))) w rfl _ parent parentInv
    reciprocal pivot unit io roles f p node scalar arity st free fits cap

theorem five_packed_root_closed [M8.Machine.Net] {Node : Type*} (layout : Node → Descriptor)
    (child : Node → Fin nodeChildren5.length → Node) (steps : Node → ℕ)
    (root : Node) (depth u tapes push entryTapes returnTapes : ℕ) {τ lam K C₁ : ℝ}
    (hτ : 0 ≤ τ) (hτl : τ ≤ lam) (hlam : 1 - bitSaving < lam) (hK : 1 ≤ K)
    (hC₁ : 0 ≤ C₁) (hu : 1 ≤ u)
    (width : 64^depth ∣ (layout root).width) (rows : 142080^depth ∣ (layout root).rows)
    (stop : (layout root).width * 42^depth ≤ u * 64^depth)
    (positive : 0 < volume prime (layout root))
    (rootLeaf : (layout root).width ≤ u → ∃ d w, 0 < d ∧ d ≤ 42 ∧
      (layout root).width = d*(w+1) ∧
      steps root ≤ packedCoordinatesTime d (volume prime (layout root)) w tapes push entryTapes returnTapes)
    (childLeaf : ∀ x, u < (layout x).width → 0 < volume prime (layout x) →
      64 ∣ (layout x).width → 142080 ∣ (layout x).rows → ∀ i, (layout (child x i)).width ≤ u →
      steps (child x i) ≤ packedCoordinatesTime nodeChildren5[i.val] (volume prime (layout (child x i)))
        ((layout x).width/64-1) tapes push entryTapes returnTapes)
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
    positive _ _ physical hcost
  · unfold packedCoordinatesRate weightedLeafRate
    positivity
  · intro small
    obtain ⟨d,w,active,rankBound,split,run⟩ := rootLeaf small
    exact packedCoordinates_steps_linear _ (M8.RevMachine.LeafCore.positive_of_volume positive)
      d 42 w tapes push entryTapes returnTapes _ active rankBound split run
  · intro x large pos div rows i childPos small
    have atom : 0 < (layout x).width / 64 :=
      Nat.div_pos (Nat.le_of_dvd (Nat.zero_lt_of_lt large) div) (by decide)
    apply packedCoordinates_steps_linear _ (M8.RevMachine.LeafCore.positive_of_volume childPos)
      _ 42 _ _ _ _ _ _ (scheduledRank_pos i) (nodeChildren5_le i) _ (childLeaf x large pos div rows i small)
    rw [physical x large pos div rows i]
    change _ * _ = _ * _
    congr 1
    omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
