import IntegerMultBounds.Machine.PackedArith
import IntegerMultBounds.Compact.PowerTwoDigits
import IntegerMultBounds.Compact.PackedControl

/-! The forward packed program on tapes computes `packedEarly` in the
radices `2^q` and `2^b`: each gathered offset word packs as the corresponding
integer offset, each modular transduction is the corresponding modular
update, so the final words are exactly the packed program's output integers. -/

namespace IntegerMultBounds.Compact.PowerTwo

open IntegerMultBounds.Counter (value)
open IntegerMultBounds.Machine.PackedArith
open IntegerMultBounds.Machine.Gather (field gather digitWord)
open IntegerMultBounds.Machine.ColumnTransducer (addRule_value subRule_value)
open Radix

/-- A control bit as an integer. -/
def ctrl (z : Bool) : ℤ := if z then 1 else 0

theorem zip_maps {α β γ δ : Type*} (f : β → γ → δ) (g : α → β) (h : α → γ) (xs : List α) :
    List.zipWith f (xs.map g) (xs.map h) = xs.map (fun x => f (g x) (h x)) := by
  induction xs <;> simp_all

theorem list_eq_range (l : List Bool) : l = (List.range l.length).map (fun i => l.getD i false) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

theorem pack_sub (B : ℤ) (xs ys : List ℤ) (hlen : xs.length = ys.length) :
    pack B (List.zipWith (fun x y => x - y) xs ys) = pack B xs - pack B ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [pack]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.zipWith_cons_cons, pack, ih ys (by simpa using hlen)]
      ring

section Offsets

variable (q b : ℕ) (hb : 1 ≤ b) (hbq : b + 1 ≤ q) (Z : List Bool)

/-- The masked, shifted blocks of a word of `n·b` bits pack as `2 z_i w_i`. -/
theorem maskShift_value (X : List Bool) (hX : X.length = Z.length * b) :
    (value (gather (fun x z => x && z) (maskShift q b hb hbq) X Z Z.length) : ℤ) =
      pack ((2 : ℤ) ^ q) (List.zipWith (fun z w => 2 * z * w) (Z.map ctrl)
        (digits ((2 : ℤ) ^ b) Z.length (value X))) := by
  rw [value_gather, digits_blocks X b Z.length hX, blockValues]
  conv_rhs => rw [list_eq_range Z, List.map_map, List.length_map, List.length_range, zip_maps]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp, value_digitWord, maskShift, value_map_and, add_zero]
  cases Z.getD i false <;> simp [ctrl]

/-- The controls at stride `q` pack as the control integers. -/
theorem controls_value (X : List Bool) (_hX : Z.length ≤ X.length) :
    (value (gather (fun _ z => z) (controlsAt q b hb hbq) X Z Z.length) : ℤ) =
      pack ((2 : ℤ) ^ q) (Z.map ctrl) := by
  rw [value_gather]
  conv_rhs => rw [list_eq_range Z, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp, value_digitWord, controlsAt, field, List.range_one, List.map_cons,
    List.map_nil, pow_zero, one_mul, value_singleton]
  cases Z.getD i false <;> simp [ctrl]

/-- The parities of the blocks of a word of `n·q` bits pack as the digit parities. -/
theorem parity_value (X : List Bool) (hX : X.length = Z.length * q) :
    (value (gather (fun x _ => x) (parity q b hb hbq) X Z Z.length) : ℤ) =
      pack ((2 : ℤ) ^ b) ((digits ((2 : ℤ) ^ q) Z.length (value X)).map (· % 2)) := by
  rw [value_gather, digits_blocks X q Z.length hX, blockValues, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp, value_digitWord, parity, pow_zero, one_mul, add_zero, List.map_id']
  exact value_field_one X (i * q) q (by omega)

/-- The toggled parities pack as the digit parities plus the controls modulo two. -/
theorem toggle_value (X : List Bool) (hX : X.length = Z.length * q) :
    (value (gather (fun x z => xor x z) (parity q b hb hbq) X Z Z.length) : ℤ) =
      pack ((2 : ℤ) ^ b) (List.zipWith (fun v z => (v % 2 + z) % 2)
        (digits ((2 : ℤ) ^ q) Z.length (value X)) (Z.map ctrl)) := by
  rw [value_gather, digits_blocks X q Z.length hX, blockValues]
  conv_rhs => rw [list_eq_range Z, List.map_map, List.length_map, List.length_range, zip_maps]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp, value_digitWord, parity, pow_zero, one_mul, add_zero]
  rw [← value_field_one X (i * q) q (by omega)]
  simp only [field, List.range_one, List.map_cons, List.map_nil, add_zero, value_singleton]
  cases X.getD (i * q) false <;> cases Z.getD i false <;> simp [ctrl]

end Offsets

section Lines

variable (q b : ℕ) (hb : 1 ≤ b) (hbq : b + 1 ≤ q) (V W Z : List Bool)
  (hV : V.length = Z.length * q) (hW : W.length = Z.length * b)

theorem addMod_value (xs ys : List Bool) (hlen : xs.length = ys.length) :
    (value (Machine.ColumnTransducer.digits Machine.ColumnTransducer.addRule 0 (xs.zip ys)) : ℤ) =
      ((value xs : ℤ) + value ys) % 2 ^ xs.length := by
  rw [addRule_value xs ys hlen]; push_cast; rfl

theorem pow_blocks (n w : ℕ) : ((2 : ℤ) ^ w) ^ n = 2 ^ (n * w) := by
  rw [← pow_mul, mul_comm]

include hV hW in
/-- The forward program's words are `packedEarly` in the power-of-two radices. -/
theorem forward_value :
    ((value (v2 q b hb hbq V W Z) : ℤ), (value (w2 q b hb hbq V W Z) : ℤ)) =
      packedEarly ((2 : ℤ) ^ q) ((2 : ℤ) ^ b) (Z.map ctrl) (value V) (value W) := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := lengths q b hb hbq V W Z hV hW
  have hn : (Z.map ctrl).length = Z.length := by simp
  -- line 1
  have hv1 : (value (v1 q b hb hbq V W Z) : ℤ) =
      ((value V : ℤ) + pack ((2 : ℤ) ^ q) (List.zipWith (fun z w => 2 * z * w) (Z.map ctrl)
        (digits ((2 : ℤ) ^ b) Z.length (value W)))) % ((2 : ℤ) ^ q) ^ Z.length := by
    rw [v1, addMod_value _ _ (by rw [hV, l1]), off1, maskShift_value q b hb hbq Z W hW, hV, pow_blocks]
  -- line 2
  have hw1 : (value (w1 q b hb hbq V W Z) : ℤ) =
      ((value W : ℤ) + pack ((2 : ℤ) ^ b)
        ((digits ((2 : ℤ) ^ q) Z.length (value (v1 q b hb hbq V W Z))).map (· % 2))) %
        ((2 : ℤ) ^ b) ^ Z.length := by
    rw [w1, addMod_value _ _ (by rw [hW, l3]), off2, parity_value q b hb hbq Z _ l2, hW, pow_blocks]
  -- line 3
  have ht1 : (value (t1 q b hb hbq V W Z) : ℤ) =
      ((value (v1 q b hb hbq V W Z) : ℤ) + pack ((2 : ℤ) ^ q) (Z.map ctrl)) % ((2 : ℤ) ^ q) ^ Z.length := by
    rw [t1, addMod_value _ _ (by rw [l2, l5]), off3a, controls_value q b hb hbq Z W (by
      rw [hW]; exact Nat.le_mul_of_pos_right _ hb), l2, pow_blocks]
  have hv2 : (value (v2 q b hb hbq V W Z) : ℤ) =
      ((value (t1 q b hb hbq V W Z) : ℤ) - pack ((2 : ℤ) ^ q) (List.zipWith (fun z w => 2 * z * w)
        (Z.map ctrl) (digits ((2 : ℤ) ^ b) Z.length (value (w1 q b hb hbq V W Z))))) %
        ((2 : ℤ) ^ q) ^ Z.length := by
    rw [v2, subRule_value _ _ (by rw [l6, l7]), off3b, maskShift_value q b hb hbq Z _ l4, l6, pow_blocks]
  -- line 4
  have hw2 : (value (w2 q b hb hbq V W Z) : ℤ) =
      ((value (w1 q b hb hbq V W Z) : ℤ) - pack ((2 : ℤ) ^ b) (List.zipWith (fun v z => (v % 2 + z) % 2)
        (digits ((2 : ℤ) ^ q) Z.length (value (v2 q b hb hbq V W Z))) (Z.map ctrl))) %
        ((2 : ℤ) ^ b) ^ Z.length := by
    rw [w2, subRule_value _ _ (by rw [l4, l9]), off4, toggle_value q b hb hbq Z _ l8, l4, pow_blocks]
  -- the signed third line
  have hzip : ∀ (C D : List ℤ), List.zipWith (fun z w => z * (1 - 2 * w)) C D =
      List.zipWith (fun x y => x - y) C (List.zipWith (fun z w => 2 * z * w) C D) := by
    intro C
    induction C with
    | nil => intro D; simp
    | cons c C ih =>
      intro D
      cases D with
      | nil => simp
      | cons d D => simp only [List.zipWith_cons_cons, ih]; congr 1; ring
  have hsigned : pack ((2 : ℤ) ^ q) (List.zipWith (fun z w => z * (1 - 2 * w)) (Z.map ctrl)
      (digits ((2 : ℤ) ^ b) Z.length (value (w1 q b hb hbq V W Z)))) =
      pack ((2 : ℤ) ^ q) (Z.map ctrl) - pack ((2 : ℤ) ^ q) (List.zipWith (fun z w => 2 * z * w)
        (Z.map ctrl) (digits ((2 : ℤ) ^ b) Z.length (value (w1 q b hb hbq V W Z)))) := by
    have hd : (digits ((2 : ℤ) ^ b) Z.length (value (w1 q b hb hbq V W Z))).length = Z.length :=
      digits_length _ _ _
    rw [hzip, pack_sub ((2 : ℤ) ^ q) (Z.map ctrl) _ (by rw [hn, List.length_zipWith, hn, hd, min_self])]
  have hv2' : (value (v2 q b hb hbq V W Z) : ℤ) =
      ((value (v1 q b hb hbq V W Z) : ℤ) + pack ((2 : ℤ) ^ q) (List.zipWith (fun z w => z * (1 - 2 * w))
        (Z.map ctrl) (digits ((2 : ℤ) ^ b) Z.length (value (w1 q b hb hbq V W Z))))) %
        ((2 : ℤ) ^ q) ^ Z.length := by
    rw [hv2, ht1, hsigned, Int.sub_emod, Int.emod_emod, ← Int.sub_emod, add_sub_assoc]
  simp only [packedEarly, hn]
  rw [Prod.mk.injEq, ← hv1, ← hw1, ← hv2']
  exact ⟨rfl, hw2⟩

end Lines

end IntegerMultBounds.Compact.PowerTwo
