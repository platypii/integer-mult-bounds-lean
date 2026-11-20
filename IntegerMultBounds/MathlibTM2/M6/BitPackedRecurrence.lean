module

public import IntegerMultBounds.MathlibTM2.M6.BitDescriptorRecurrence
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodParentSetup
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodRecordRoundTrip

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

open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host in
noncomputable def scheduledAdapterTime {P U : Type} [Fintype P] {T A : ℕ}
    (body : P → Pr P T 217 A U) (machine : Fin 55 ↪ Fin T) (digits : ℕ)
    (v : Descriptor) (w : ℕ) (i : Fin nodeChildren5.length) (budget : ℕ) : ℕ :=
  let parent := role v 142080
  let r := nodeChildren5[i.val]
  let g := 64-r
  let hr := (nodeChildren5_le i).trans (by decide : 42 ≤ 64)
  let H := (prime^(w+1)).size
  let W := parent.beforeRows*parent.rows*parent.beforeH*parent.between*parent.afterD
  let K := digits*H+1
  let middle := (((List.finRange r).map fun j => childWeightTime prime w H j.val).sum+1 +
    dimensionTime H K (g+g)) + (budget+2+(2*(r*H+r*H+((g+g)*H+K))+7))
  1 + goodIncomingTime body machine prime w W H W.size r hr + middle +
    (1 + goodOutgoingTime body machine prime w W H W.size r hr)

open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host in
/-- Every selected rank admits the same adapter rate per child-volume symbol.
The recursive budget is passed through once, including for repeated ranks. -/
theorem scheduledAdapter_time {P U : Type} [Fintype P] {T A : ℕ}
    (body : P → Pr P T 217 A U) (machine : Fin 55 ↪ Fin T) (digits : ℕ) :
    ∃ C : ℕ, ∀ (v : Descriptor) w (i : Fin nodeChildren5.length) budget,
      v.width = 64*(w+1) → 0 < volume prime (role v 142080) →
      scheduledAdapterTime body machine digits v w i budget ≤
        budget + C * volume prime (scheduledChild prime v i) := by
  classical
  have bounds (j : Fin 65) := goodRecordTime_volume_le body machine j.val (64-j.val) digits
    (show 64 = j.val+(64-j.val) by omega) (by decide) (by omega)
  choose rate priced using bounds
  refine ⟨∑ j, rate j,?_⟩
  intro v w i budget split pos
  unfold scheduledAdapterTime
  dsimp only
  let parent := role v 142080
  let r := nodeChildren5[i.val]
  have hr : r ≤ 64 := (nodeChildren5_le i).trans (by decide : 42 ≤ 64)
  let W := parent.beforeRows*parent.rows*parent.beforeH*parent.between*parent.afterD
  let j : Fin 65 := ⟨r,by omega⟩
  have positive : 0 < W := by
    dsimp only [W]
    change 0 < volume prime parent at pos
    simp only [volume, Nat.pos_iff_ne_zero, mul_ne_zero_iff] at pos ⊢
    tauto
  have cost := priced j w W budget positive
  have same : volume prime (scheduledChild prime v i) = volume prime parent := by
    simp only [scheduledChild,split,Nat.mul_div_cancel_left _ (by decide : 0 < 64)]
    apply rankDescriptor_volume
    change v.width = _
    rw [split,← Nat.add_mul,Nat.add_sub_of_le hr]
  have size : (prime^(w+1))^(64+64)*W = volume prime parent := by
    change _ = parent.beforeRows*parent.rows*parent.beforeH*prime^v.width*parent.between*prime^v.width*parent.afterD
    rw [split,pow_add, Nat.mul_comm 64 (w+1),pow_mul]
    dsimp only [W]
    ring
  exact cost.trans (Nat.add_le_add_left ((Nat.mul_le_mul_right _
    (Finset.single_le_sum (fun k _ => Nat.zero_le (rate k)) (Finset.mem_univ j))).trans_eq
    (by rw [size,same])) _)

open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host in
/-- Sum the hosted adapter bills for the selected PR589 schedule in parent
volume units, keeping each recursive budget at its own occurrence. -/
theorem scheduledAdapters_node_time {P U : Type} [Fintype P] {T A : ℕ}
    (body : P → Pr P T 217 A U) (machine : Fin 55 ↪ Fin T) (digits : ℕ) :
    ∃ C : ℕ, ∀ (v : Descriptor) w (budget : Fin nodeChildren5.length → ℕ),
      v.width = 64*(w+1) → 142080 ∣ v.rows → 0 < volume prime v →
      (∑ i, scheduledAdapterTime body machine digits v w i (budget i)) * 142080 ≤
        (∑ i, budget i) * 142080 + nodeChildren5.length * C * volume prime v := by
  obtain ⟨C,priced⟩ := scheduledAdapter_time body machine digits
  refine ⟨C,?_⟩
  intro v w budget width rows pos
  have parent := role_volume_mul prime 142080 v rows
  have live := Nat.pos_of_mul_pos_right (parent.symm ▸ pos)
  have cost (i : Fin nodeChildren5.length) := Nat.mul_le_mul_right 142080
    (priced v w i (budget i) width live)
  have piece (i : Fin nodeChildren5.length) := (rankDescriptor_role_size (M := prime)
    v 142080 64 (w+1) width ((nodeChildren5_le i).trans (by decide : 42 ≤ 64)) rows).2
  have child (i : Fin nodeChildren5.length) :
      volume prime (scheduledChild prime v i)*142080 = volume prime v := by
    simpa only [scheduledChild,width,Nat.mul_div_cancel_left _ (by decide : 0 < 64)] using piece i
  simp only [Nat.add_mul,Nat.mul_assoc,child] at cost
  rw [Finset.sum_mul,Finset.sum_mul]
  simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_id,Nat.mul_assoc] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => cost i)

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
      steps root ≤ pivotSetupTime 64 d w (prime^(w+1)).size + packedCoordinatesTime d (volume prime (layout root)) w tapes push entryTapes returnTapes + recordRoundTripRate 64*volume prime (layout root))
    (childLeaf : ∀ x, u < (layout x).width → 0 < volume prime (layout x) →
      64 ∣ (layout x).width → 142080 ∣ (layout x).rows → ∀ i, (layout (child x i)).width ≤ u →
      steps (child x i) ≤ pivotSetupTime 64 nodeChildren5[i.val] ((layout x).width/64-1)
        (prime^((layout x).width/64-1+1)).size + packedCoordinatesTime nodeChildren5[i.val] (volume prime (layout (child x i)))
        ((layout x).width/64-1) tapes push entryTapes returnTapes + recordRoundTripRate 64*volume prime (layout (child x i)))
    (physical : ∀ x, u < (layout x).width → 0 < volume prime (layout x) →
      64 ∣ (layout x).width → 142080 ∣ (layout x).rows → ∀ i, layout (child x i) = scheduledChild prime (layout x) i)
    (hcost : ∀ x, u < (layout x).width → 0 < volume prime (layout x) →
      64 ∣ (layout x).width → 142080 ∣ (layout x).rows →
      (steps x : ℝ) ≤ C₁ * ((K * (layout x).width) ^ τ + 1) * volume prime (layout x) +
        ((∑ i, steps (child x i) : ℕ) : ℝ)) :
    (steps root : ℝ) ≤
      (2 * C₁ / (1 - ((42 : ℝ) / 64) ^ (lam - (1 - bitSaving))) * K ^ τ * ((layout root).width : ℝ) ^ lam +
      ((pivotSetupTime 64 42 1 1 * (2*(prime.size+1)^2) + recordRoundTripRate 64 : ℕ) + packedCoordinatesRate 42 tapes push entryTapes returnTapes) * ((layout root).width : ℝ) ^ (1 - bitSaving) * (u : ℝ) ^ (1 - (1 - bitSaving))) * volume prime (layout root) := by
  apply five_root_closed prime layout child steps root depth u hτ hτl hlam hK _ hC₁ hu width rows stop
    positive _ _ physical hcost
  · apply add_nonneg (Nat.cast_nonneg _)
    unfold packedCoordinatesRate weightedLeafRate
    positivity
  · intro small
    obtain ⟨d,w,active,rankBound,split,run⟩ := rootLeaf small
    exact goodCoordinates_steps_linear _ (M8.RevMachine.LeafCore.positive_of_volume positive)
      64 d 42 w tapes push entryTapes returnTapes (recordRoundTripRate 64) _ active rankBound split run
  · intro x large pos div rows i childPos small
    have atom : 0 < (layout x).width / 64 :=
      Nat.div_pos (Nat.le_of_dvd (Nat.zero_lt_of_lt large) div) (by decide)
    apply goodCoordinates_steps_linear _ (M8.RevMachine.LeafCore.positive_of_volume childPos)
      64 _ 42 _ _ _ _ _ (recordRoundTripRate 64) _ (scheduledRank_pos i) (nodeChildren5_le i) _ (childLeaf x large pos div rows i small)
    rw [physical x large pos div rows i]
    change _ * _ = _ * _
    congr 1
    omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
