import IntegerMultBounds.Machine.ScalingStream
import IntegerMultBounds.Machine.ScalingPartitionData
import IntegerMultBounds.Machine.BlockNegationData
import IntegerMultBounds.Machine.ScalingInverseExecution
import IntegerMultBounds.Networks.Shared50AffineCoefficients

/-! Pure semantic orientation of literal payload scaling and ordered-affine
coordinate updates. Positive merging transports a source block y to c*y;
inverse scatter reads input c*y at output y. Whole blocks remain opaque values.
No additional machine execution or running-time theorem is asserted here. -/

namespace IntegerMultBounds.Machine.ScalingAffineBridge

open Networks

/-- Positive scaling's source index for a destination z. -/
def inverseAddress {c : ℕ} (hc : 0 < c) (Q z : ℕ) : ℕ :=
  ScalingPieces.restore Q c z (ScalingControl.select hc Q z).val

/-- The exact opaque-block output of the positive merge. -/
def positiveBlocks {α : Type*} {c : ℕ} (hc : 0 < c) (Q : ℕ) (payload : ℕ → α) : List α :=
  (List.range Q).map (fun z => payload (inverseAddress hc Q z))

/-- The exact opaque-block output of inverse scatter followed by concatenation. -/
def inverseBlocks {α : Type*} (Q c : ℕ) (payload : ℕ → α) : List α :=
  (List.range Q).map (fun (y : ℕ) => payload (ScalingPieces.output Q c y))

theorem execution_output {c : ℕ} (hc : 0 < c) (Q : ℕ) (payload : ℕ → List (Fin 4)) :
    ScalingMerge.outputPrefix hc Q Q payload = (positiveBlocks hc Q payload).flatten := rfl

theorem stream_output {c : ℕ} (hc : 0 < c) (Q n : ℕ) (payload : ℕ → ℕ → List (Fin 4)) :
    ScalingStream.outputPrefix hc Q n payload =
      ((List.range n).map (fun i => (positiveBlocks hc Q (payload i)).flatten)).flatten := rfl

theorem inverse_output {c : ℕ} (hc : 0 < c) (Q : ℕ) (payload : ℕ → List (Fin 4)) :
    (((List.range c).map (fun j => ScalingMergeData.blocks Q c j
      (fun y => payload (ScalingPieces.output Q c y)))).flatten).flatten =
      (inverseBlocks Q c payload).flatten := ScalingPartitionData.inverse_blocks hc payload

/-- Natural modular multiplication is the same multiplication in ZMod. -/
theorem output_cast (Q c y : ℕ) :
    (ScalingPieces.output Q c y : ZMod Q) = (c : ZMod Q)*(y : ZMod Q) := by
  simp [ScalingPieces.output]

/-- The arithmetic reconstruction used by the actual merge is the modular
inverse coefficient, including composite moduli and multiplier magnitudes > Q. -/
theorem inverseAddress_cast {Q c z : ℕ} (hc : 0 < c) (hcop : c.Coprime Q) :
    (inverseAddress hc Q z : ZMod Q) = (c : ZMod Q)⁻¹*(z : ZMod Q) := by
  have hp := ScalingPieces.restore_product (ScalingControl.select_admissible hc hcop z)
  have he := congrArg (fun n : ℕ => (n : ZMod Q)) hp
  simp only [Nat.cast_mul,Nat.cast_add,ZMod.natCast_self,mul_zero,add_zero] at he
  have hu := (ZMod.isUnit_iff_coprime c Q).mpr hcop
  calc
    (inverseAddress hc Q z : ZMod Q) =
        ((c : ZMod Q)⁻¹*(c : ZMod Q))*(inverseAddress hc Q z : ZMod Q) := by
      rw [ZMod.inv_mul_of_unit _ hu,one_mul]
    _ = (c : ZMod Q)⁻¹*((c : ZMod Q)*(inverseAddress hc Q z : ZMod Q)) := mul_assoc _ _ _
    _ = (c : ZMod Q)⁻¹*(z : ZMod Q) := congrArg (fun x => (c : ZMod Q)⁻¹*x) he

/-- Multiplication by any fixed denominator commutes with the numerator's
canonical inverse source index. Both sides are actual natural addresses < Q. -/
theorem inverseAddress_output {Q a y : ℕ} (hQ : 0 < Q) (ha : 0 < a)
    (hcop : a.Coprime Q) (d : ℕ) :
    inverseAddress ha Q (ScalingPieces.output Q d y) =
      ScalingPieces.output Q d (inverseAddress ha Q y) := by
  have hl : inverseAddress ha Q (ScalingPieces.output Q d y) < Q :=
    ScalingPieces.restore_lt ha (ScalingPieces.output_lt hQ)
      (ScalingControl.select_admissible ha hcop _)
  have hr : ScalingPieces.output Q d (inverseAddress ha Q y) < Q := ScalingPieces.output_lt hQ
  have he : (inverseAddress ha Q (ScalingPieces.output Q d y) : ZMod Q) =
      (ScalingPieces.output Q d (inverseAddress ha Q y) : ZMod Q) := by
    rw [inverseAddress_cast ha hcop,output_cast,output_cast,inverseAddress_cast ha hcop]
    ring
  have hv := congrArg ZMod.val he
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hl,Nat.mod_eq_of_lt hr] using hv

/-- The two literal unsigned stage orders return exactly the same block list,
without assuming that an arbitrary natural-indexed payload is periodic. -/
theorem stages_commute {α : Type*} {Q a : ℕ} (hQ : 0 < Q) (ha : 0 < a)
    (hcop : a.Coprime Q) (d : ℕ) (payload : ℕ → α) :
    inverseBlocks Q d (fun y => payload (inverseAddress ha Q y)) =
      positiveBlocks ha Q (fun y => payload (ScalingPieces.output Q d y)) := by
  unfold inverseBlocks positiveBlocks
  apply List.map_congr_left
  intro y _
  change payload (inverseAddress ha Q (ScalingPieces.output Q d y)) = _
  rw [inverseAddress_output hQ ha hcop d]

/-- Pointwise list semantics of positive payload transport, with no assumptions
on the payload beyond its indexing by canonical modular addresses. -/
theorem positive_get {α : Type*} {Q c z : ℕ} (hc : 0 < c) (hcop : c.Coprime Q)
    (hz : z < Q) (payload : ZMod Q → α) :
    (positiveBlocks hc Q (fun y => payload (y : ZMod Q)))[z]? =
      some (payload ((c : ZMod Q)⁻¹*(z : ZMod Q))) := by
  rw [positiveBlocks,List.getElem?_map,List.getElem?_range hz,Option.map_some,inverseAddress_cast hc hcop]

theorem inverse_get {α : Type*} {Q c z : ℕ} (hz : z < Q) (payload : ZMod Q → α) :
    (inverseBlocks Q c (fun y => payload (y : ZMod Q)))[z]? =
      some (payload ((c : ZMod Q)*(z : ZMod Q))) := by
  rw [inverseBlocks,List.getElem?_map,List.getElem?_range hz,Option.map_some,output_cast]

theorem inverse_execution_output (Q c : ℕ) (payload : ℕ → List (Fin 4)) :
    ScalingInverseExecution.outputWord Q c payload = (inverseBlocks Q c payload).flatten := rfl

/-- Pointwise natural address negation, with address zero fixed. -/
def negAddress (Q y : ℕ) : ℕ := (Q-y)%Q

private theorem negAddress_involutive {Q y : ℕ} (hy : y < Q) :
    negAddress Q (negAddress Q y) = y := by
  by_cases hz : y = 0
  · subst y
    simp [negAddress]
  · have hsub : Q-y < Q := by omega
    have hsub2 : Q-(Q-y) = y := by omega
    simp only [negAddress,Nat.mod_eq_of_lt hsub,hsub2,Nat.mod_eq_of_lt hy]

private theorem negAddress_cast {Q y : ℕ} (hy : y < Q) :
    (negAddress Q y : ZMod Q) = -(y : ZMod Q) := by
  simp [negAddress,Nat.cast_sub hy.le]

/-- The literal first-block-preserving tail reversal is exactly modular
coordinate negation, including each complete block's internal symbol order. -/
theorem negate_modular {α : Type*} (Q : ℕ) (payload : ZMod Q → List α) :
    BlockNegationData.negate ((List.range Q).map (fun (y : ℕ) => payload (y : ZMod Q))) =
      (List.range Q).map (fun (y : ℕ) => payload (-(y : ZMod Q))) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hiQ : i < Q := by simpa using hi
    have hQ : 0 < Q := by omega
    have hy : negAddress Q i < Q := Nat.mod_lt _ hQ
    have hh := BlockNegationData.block_destination
      ((List.range Q).map (fun (y : ℕ) => payload (y : ZMod Q))) (negAddress Q i) (by simpa using hy)
    have hindex : (((List.range Q).map (fun (y : ℕ) => payload (y : ZMod Q))).length-negAddress Q i)%
        ((List.range Q).map (fun (y : ℕ) => payload (y : ZMod Q))).length = i := by
      simpa only [List.length_map,List.length_range,negAddress] using negAddress_involutive hiQ
    simpa only [hindex,List.getElem_map,List.getElem_range,negAddress_cast hiQ] using hh

/-- Canonical list law for the positive machine, usable as a rewrite in a
composition of opaque-block permutations. -/
theorem positive_modular {α : Type*} {c : ℕ} (hc : 0 < c) (Q : ℕ) (hcop : c.Coprime Q)
    (payload : ZMod Q → α) :
    positiveBlocks hc Q (fun y => payload (y : ZMod Q)) =
      (List.range Q).map (fun (y : ℕ) => payload ((c : ZMod Q)⁻¹*(y : ZMod Q))) := by
  unfold positiveBlocks
  apply List.map_congr_left
  intro y _
  change payload (inverseAddress hc Q y : ZMod Q) = _
  rw [inverseAddress_cast hc hcop]

theorem inverse_modular {α : Type*} (Q c : ℕ) (payload : ZMod Q → α) :
    inverseBlocks Q c (fun y => payload (y : ZMod Q)) =
      (List.range Q).map (fun (y : ℕ) => payload ((c : ZMod Q)*(y : ZMod Q))) := by
  unfold inverseBlocks
  apply List.map_congr_left
  intro y _
  change payload (ScalingPieces.output Q c y : ZMod Q) = _
  rw [output_cast]

/-- Exact opaque-block composition: inverse-denominator output feeds positive
numerator scaling, followed by the actual block-negation recipe when needed. -/
def signedBlocks {α : Type*} {a : ℕ} (ha : 0 < a) (Q d : ℕ) (negative : Bool)
    (payload : ℕ → List α) : List (List α) :=
  let positive := positiveBlocks ha Q (fun y => payload (ScalingPieces.output Q d y))
  if negative then BlockNegationData.negate positive else positive

/-- Exact list transform law, fixing every inverse/sign orientation in the
three-stage rational scaling recipe. -/
theorem signedBlocks_modular {α : Type*} {a : ℕ} (ha : 0 < a) (Q d : ℕ)
    (hcop : a.Coprime Q) (negative : Bool) (payload : ZMod Q → List α) :
    signedBlocks ha Q d negative (fun y => payload (y : ZMod Q)) =
      (List.range Q).map (fun (y : ℕ) => payload ((d : ZMod Q)*
        ((a : ZMod Q)⁻¹*((if negative then -1 else 1)*(y : ZMod Q))))) := by
  have hp : positiveBlocks ha Q (fun y => payload (ScalingPieces.output Q d y : ZMod Q)) =
      (List.range Q).map (fun (y : ℕ) => payload ((d : ZMod Q)*((a : ZMod Q)⁻¹*(y : ZMod Q)))) := by
    simp only [output_cast]
    exact positive_modular ha Q hcop (fun y => payload ((d : ZMod Q)*y))
  unfold signedBlocks
  rw [hp]
  cases negative
  · simp
  · simpa only [ite_true,neg_one_mul] using
      negate_modular Q (fun y => payload ((d : ZMod Q)*((a : ZMod Q)⁻¹*y)))

/-- The resulting lookup transports each original block to the signed rational
forward destination, using only unit cancellation, valid at every prime power. -/
theorem signed_destination {α : Type*} {Q a d : ℕ} (ha : a.Coprime Q) (hd : d.Coprime Q)
    (sign : ZMod Q) (hs : sign*sign = 1) (payload : ZMod Q → α) (x : ZMod Q) :
    payload ((d : ZMod Q)*((a : ZMod Q)⁻¹*
      (sign*(sign*((a : ZMod Q)*((d : ZMod Q)⁻¹*x)))))) = payload x := by
  congr 1
  calc
    (d : ZMod Q)*((a : ZMod Q)⁻¹*(sign*(sign*((a : ZMod Q)*((d : ZMod Q)⁻¹*x))))) =
      ((d : ZMod Q)*(d : ZMod Q)⁻¹)*((a : ZMod Q)⁻¹*(a : ZMod Q))*(sign*sign)*x := by ring
    _ = x := by
      rw [ZMod.coe_mul_inv_eq_one d hd,
        ZMod.inv_mul_of_unit _ ((ZMod.isUnit_iff_coprime a Q).mpr ha),hs]
      simp

/-- Actual schedule specialization of the exact list recipe: the block at the
forward rational-scaled destination is precisely its original opaque payload.
This closes the sign/numerator/denominator algebra without unfolding schedules. -/
theorem actual_signed_get {α : Type*} {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (b : ℕ) (payload : ZMod (Shared50ModularControl.prime^b) → List α)
    (x : ZMod (Shared50ModularControl.prime^b)) :
    (signedBlocks (Shared50AffineCoefficients.unit_recipe hr b).1
      (Shared50ModularControl.prime^b) r.den (decide (r.num < 0))
      (fun y => payload (y : ZMod (Shared50ModularControl.prime^b))))[(Swap.Modular.ratMod (Shared50ModularControl.prime^b) r*x).val]? = some (payload x) := by
  let : NeZero (Shared50ModularControl.prime^b) :=
    ⟨pow_ne_zero b Shared50ModularControl.prime_prime.ne_zero⟩
  obtain ⟨ha,hd,hac,hdc,hrecipe⟩ := Shared50AffineCoefficients.unit_recipe hr b
  have hsign : (if decide (r.num < 0) then (-1 : ZMod (Shared50ModularControl.prime^b)) else 1) =
      if 0 ≤ r.num then 1 else -1 := by
    by_cases h : 0 ≤ r.num
    · simp [h,not_lt.mpr h]
    · simp [h,lt_of_not_ge h]
  have hsquare : ((if 0 ≤ r.num then 1 else -1) : ZMod (Shared50ModularControl.prime^b))*
      (if 0 ≤ r.num then 1 else -1) = 1 := by
    split_ifs <;> simp
  rw [signedBlocks_modular _ _ _ hac,List.getElem?_map,
    List.getElem?_range (ZMod.val_lt _),Option.map_some,ZMod.natCast_zmod_val,hsign,hrecipe x]
  exact congrArg some (signed_destination hac hdc _ hsquare payload x)

section Coordinate
variable {ι : Type*} [LinearOrder ι] {Q : ℕ}

/-- One fixed fiber, varying exactly the target coordinate. Its payload may
include all later-coordinate blocks without inspecting their internal order. -/
def fiber (x : ι → ZMod Q) (target : ι) (y : ZMod Q) : ι → ZMod Q :=
  Function.update x target y

/-- OrderedAffine scaling acts on the varying fiber coordinate alone. -/
theorem execute_fiber (x : ι → ZMod Q) (target : ι) (a y : ZMod Q) :
    OrderedAffine.execute (.scale target a) (fiber x target y) = fiber x target (a*y) := by
  simp only [OrderedAffine.execute,fiber,Function.update_self,Function.update_idem]

/-- Forward block destination is exactly the address update of OrderedAffine. -/
theorem positive_destination (x : ι → ZMod Q) (target : ι) (c y : ℕ) :
    OrderedAffine.execute (.scale target (c : ZMod Q)) (fiber x target (y : ZMod Q)) =
      fiber x target (ScalingPieces.output Q c y : ZMod Q) := by
  rw [execute_fiber,output_cast]

/-- The block stored at a destination is read from its inverse affine address. -/
theorem positive_affine_get {α : Type*} {c z : ℕ} (hc : 0 < c) (hcop : c.Coprime Q)
    (hz : z < Q) (x : ι → ZMod Q) (target : ι) (payload : (ι → ZMod Q) → α) :
    (positiveBlocks hc Q (fun y => payload (fiber x target (y : ZMod Q))))[z]? =
      some (payload (OrderedAffine.execute (.scale target (c : ZMod Q)⁻¹)
        (fiber x target (z : ZMod Q)))) := by
  rw [execute_fiber]
  exact positive_get hc hcop hz (fun y => payload (fiber x target y))

/-- Inverse scatter implements coefficient c inverse, whose inverse-address
lookup is multiplication by c. This fixes the orientation of the inverse path. -/
theorem inverse_affine_get {α : Type*} {c z : ℕ} (hz : z < Q)
    (x : ι → ZMod Q) (target : ι) (payload : (ι → ZMod Q) → α) :
    (inverseBlocks Q c (fun y => payload (fiber x target (y : ZMod Q))))[z]? =
      some (payload (OrderedAffine.execute (.scale target (c : ZMod Q))
        (fiber x target (z : ZMod Q)))) := by
  rw [execute_fiber]
  exact inverse_get hz (fun y => payload (fiber x target y))

/-- Composition of target scalings multiplies coefficients in execution order. -/
theorem execute_scale_scale (x : ι → ZMod Q) (target : ι) (a b : ZMod Q) :
    OrderedAffine.execute (.scale target b) (OrderedAffine.execute (.scale target a) x) =
      OrderedAffine.execute (.scale target (b*a)) x := by
  simp only [OrderedAffine.execute,Function.update_self,Function.update_idem,mul_assoc]

/-- Actual rational-schedule coefficients are realized by denominator-inverse,
positive numerator, then optional sign. Every magnitude is a fixed positive
unit, as derived from the actual Shared50 schedule membership. -/
theorem actual_scale_recipe {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) (b : ℕ)
    (x : ι → ZMod (Shared50ModularControl.prime^b)) (target : ι) :
    OrderedAffine.run
      [.scale target (r.den : ZMod (Shared50ModularControl.prime^b))⁻¹,
       .scale target (r.num.natAbs : ZMod (Shared50ModularControl.prime^b)),
       .scale target (if 0 ≤ r.num then 1 else -1)] x =
      OrderedAffine.execute (.scale target (Swap.Modular.ratMod (Shared50ModularControl.prime^b) r)) x := by
  have hrule := (Shared50AffineCoefficients.unit_recipe hr b).2.2.2.2
  simp only [OrderedAffine.run,List.foldl_cons,List.foldl_nil,OrderedAffine.execute,
    Function.update_self,Function.update_idem]
  rw [← hrule]

end Coordinate

end IntegerMultBounds.Machine.ScalingAffineBridge
