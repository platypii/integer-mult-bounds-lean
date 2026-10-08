import IntegerMultBounds.Machine.Gather
import IntegerMultBounds.Machine.ColumnTransducer
import IntegerMultBounds.Compact.Radix

/-! Bit words as packed integers in a power-of-two radix. A word of `n·q`
bits read least significant bit first is the packed integer whose base-`2^q`
digits are the values of its `q`-bit blocks; the gather gadget's output is the
packing of its digit words; and the per-digit forms used by the compact
control arithmetic, a block masked by a control bit and shifted, a block's
parity, and a parity toggled by a control bit, have the stated values. -/

namespace IntegerMultBounds.Compact.PowerTwo

open IntegerMultBounds.Counter (value)
open IntegerMultBounds.Machine.Gather (field gather digitWord Shape)
open IntegerMultBounds.Machine.ColumnTransducer (value_append)
open Radix

section Fields

theorem field_append_right (xs ys : List Bool) (start d : ℕ) :
    field (xs ++ ys) (xs.length + start) d = field ys start d := by
  simp only [field]
  refine List.map_congr_left fun j _ => ?_
  rw [show xs.length + start + j = xs.length + (start + j) by ring, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

theorem field_take (xs : List Bool) (d : ℕ) (hd : d ≤ xs.length) : field xs 0 d = xs.take d := by
  apply List.ext_getElem
  · simp [field]; omega
  · intro j hj hj'
    simp only [field, List.getElem_map, List.getElem_range, zero_add, List.getElem_take]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp at hj; omega)]
    rfl

theorem value_replicate_false (n : ℕ) : value (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, value, ih]

theorem value_take_add_drop (V : List Bool) (q : ℕ) :
    value V = value (V.take q) + 2 ^ (V.take q).length * value (V.drop q) := by
  conv_lhs => rw [← List.take_append_drop q V]
  exact value_append _ _

/-- The base-`2^q` digit values of a word, by `q`-bit blocks. -/
def blockValues (V : List Bool) (q n : ℕ) : List ℤ :=
  (List.range n).map fun i => (value (field V (i * q) q) : ℤ)

theorem blockValues_succ (V : List Bool) (q n : ℕ) (hq : q ≤ V.length) :
    blockValues V q (n + 1) = (value (V.take q) : ℤ) :: blockValues (V.drop q) q n := by
  simp only [blockValues, List.range_succ_eq_map, List.map_cons, List.map_map, zero_mul,
    field_take V q hq]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp]
  have := field_append_right (V.take q) (V.drop q) (i * q) q
  rw [List.take_append_drop, List.length_take, min_eq_left hq] at this
  rw [show (i + 1) * q = q + i * q by ring, this]

/-- A word of `n·q` bits is the packed integer of its block values. -/
theorem digits_blocks (V : List Bool) (q n : ℕ) (hV : V.length = n * q) :
    digits ((2 : ℤ) ^ q) n (value V) = blockValues V q n := by
  induction n generalizing V with
  | zero => simp [digits, blockValues]
  | succ n ih =>
    have hq : q ≤ V.length := by rw [hV]; nlinarith
    have hsplit := value_take_add_drop V q
    rw [List.length_take, min_eq_left hq] at hsplit
    have hlt := Counter.value_lt (V.take q)
    rw [List.length_take, min_eq_left hq] at hlt
    have hdrop : (V.drop q).length = n * q := by rw [List.length_drop, hV]; ring_nf; omega
    rw [digits, blockValues_succ V q n hq, ← ih (V.drop q) hdrop]
    have hne : ((2 : ℤ) ^ q) ≠ 0 := pow_ne_zero _ two_ne_zero
    congr 1
    · rw [hsplit]
      push_cast
      rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hlt)]
    · congr 1
      rw [hsplit]
      push_cast
      rw [Int.add_mul_ediv_left _ _ hne,
        Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast hlt), zero_add]

theorem blockValues_bounded (V : List Bool) (q n : ℕ) :
    Bounded ((2 : ℤ) ^ q) (blockValues V q n) := by
  intro d hd
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hd
  have h := Counter.value_lt (field V (i * q) q)
  rw [Machine.Gather.field_length] at h
  exact ⟨by positivity, by exact_mod_cast h⟩

end Fields

section Packing

/-- A list of equally wide words packs as its values. -/
theorem value_flatten (st : ℕ) (words : List (List Bool)) (h : ∀ w ∈ words, w.length = st) :
    (value words.flatten : ℤ) = pack ((2 : ℤ) ^ st) (words.map fun w => (value w : ℤ)) := by
  induction words with
  | nil => simp [value, pack]
  | cons w rest ih =>
    rw [List.flatten_cons, value_append, h w (by simp), List.map_cons, pack, Nat.cast_add,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ih (fun w hw => h w (by simp [hw]))]

theorem gather_flatten (op : Bool → Bool → Bool) (S : Shape) (xs zs : List Bool) (n : ℕ) :
    gather op S xs zs n = ((List.range n).map (digitWord op S xs zs)).flatten := by
  induction n with
  | zero => rfl
  | succ n ih => rw [gather, ih, List.range_succ, List.map_append, List.flatten_append]; simp

/-- The gathered word packs as its digit word values. -/
theorem value_gather (op : Bool → Bool → Bool) (S : Shape) (xs zs : List Bool) (n : ℕ) :
    (value (gather op S xs zs n) : ℤ) =
      pack ((2 : ℤ) ^ S.st) ((List.range n).map fun i => (value (digitWord op S xs zs i) : ℤ)) := by
  rw [gather_flatten, value_flatten S.st _ (fun w hw => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hw
    exact Machine.Gather.digitWord_length op S xs zs i), List.map_map]
  rfl

/-- A digit word is its field combination shifted by the offset. -/
theorem value_digitWord (op : Bool → Bool → Bool) (S : Shape) (xs zs : List Bool) (i : ℕ) :
    value (digitWord op S xs zs i) =
      2 ^ S.ot * value ((field xs (i * S.sx + S.ox) S.d).map fun x => op x (zs.getD i false)) := by
  simp only [digitWord, value_append, value_replicate_false, List.length_replicate, mul_zero,
    add_zero, zero_add]

end Packing

section Forms

/-- A block masked by a control bit. -/
theorem value_map_and (w : List Bool) (z : Bool) :
    value (w.map fun x => x && z) = if z then value w else 0 := by
  cases z <;> simp [value_replicate_false]

/-- A single bit as a value. -/
theorem value_singleton (b : Bool) : value [b] = if b then 1 else 0 := by
  simp [value]

/-- The parity of a block is its first bit. -/
theorem value_field_one (V : List Bool) (start q : ℕ) (hq : 1 ≤ q) :
    (value (field V start 1) : ℤ) = (value (field V start q) : ℤ) % 2 := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have h : field V start (q' + 1) = V.getD start false :: field V (start + 1) q' := by
    simp only [field, List.range_succ_eq_map, List.map_cons, List.map_map, add_zero]
    congr 1
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp]
    congr 1
    omega
  rw [h]
  simp only [field, List.range_one, List.map_cons, List.map_nil, add_zero, value, mul_comm]
  push_cast
  rw [Int.add_mul_emod_self_left]
  cases V.getD start false <;> simp

end Forms

end IntegerMultBounds.Compact.PowerTwo
