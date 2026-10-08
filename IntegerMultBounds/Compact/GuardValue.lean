import IntegerMultBounds.Machine.GuardGadget
import IntegerMultBounds.Compact.PowerTwoDigits
import IntegerMultBounds.Compact.ExactRepair

/-! The guard test on tapes decides membership in the exceptional set: with
the constants `2B`, `L - 2B - 1` and `B - 2` as words, some flag is set
exactly when the address fails `earlyGood` in the radices `2^q`, `2^b`. -/

namespace IntegerMultBounds.Compact.PowerTwo

open IntegerMultBounds.Counter (value)
open IntegerMultBounds.Machine.GuardGadget (flagsV flagsW flagWordV flagWordW)
open IntegerMultBounds.Machine.GuardTest (orderAfter)
open IntegerMultBounds.Machine.Gather (field)
open IntegerMultBounds.Machine.BinaryCompare (rel rel_eq rel_lt)
open Radix

section Orders

theorem rel_gt (xs ys : List Bool) (hlen : xs.length = ys.length) :
    (rel .eq (xs.zip ys) = .gt) = (value ys < value xs) := by
  rw [rel_eq _ _ _ hlen]
  split_ifs <;> simp <;> omega

theorem orderAfter_lt (V C : List Bool) (start d : ℕ) (hC : C.length = d) :
    (orderAfter .eq V C start d = .lt) = (value (field V start d) < value C) := by
  rw [orderAfter, field_take C d (by omega), rel_lt _ _ (by simp [hC]), ← hC, List.take_length]

theorem orderAfter_gt (V C : List Bool) (start d : ℕ) (hC : C.length = d) :
    (orderAfter .eq V C start d = .gt) = (value C < value (field V start d)) := by
  rw [orderAfter, field_take C d (by omega), rel_gt _ _ (by simp [hC]), ← hC, List.take_length]

/-- The upper bits of a block are its value divided by two. -/
theorem value_field_shift (V : List Bool) (start q : ℕ) (hq : 1 ≤ q) :
    (value (field V (start + 1) (q - 1)) : ℤ) = (value (field V start q) : ℤ) / 2 := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have h : field V start (q' + 1) = V.getD start false :: field V (start + 1) q' := by
    simp only [field, List.range_succ_eq_map, List.map_cons, List.map_map, add_zero]
    congr 1
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp]
    congr 1
    omega
  rw [h, Nat.add_sub_cancel]
  simp only [value]
  push_cast
  rw [Int.add_mul_ediv_left _ _ two_ne_zero]
  cases V.getD start false <;> simp

end Orders

section Flags

/-- The flag words as flattened block flags. -/
theorem flagWordV_flatten (q : ℕ) (V C1 C2 : List Bool) (n : ℕ) :
    flagWordV q V C1 C2 n = ((List.range n).map (flagsV q V C1 C2)).flatten := by
  induction n with
  | zero => rfl
  | succ n ih => rw [flagWordV, ih, List.range_succ, List.map_append, List.flatten_append]; simp

theorem flagWordW_flatten (q b n : ℕ) (V W C1 C2 C3 : List Bool) (i : ℕ) :
    flagWordW q b n V W C1 C2 C3 i =
      flagWordV q V C1 C2 n ++ ((List.range i).map (flagsW b W C3)).flatten := by
  induction i with
  | zero => simp [flagWordW]
  | succ i ih => rw [flagWordW, ih, List.range_succ, List.map_append, List.flatten_append]; simp

variable (q b n : ℕ) (V W C1 C2 C3 : List Bool)
  (hV : V.length = n * q) (hW : W.length = n * b) (hq : b + 3 ≤ q)
  (hC1 : C1.length = q - 1) (hC2 : C2.length = q - 1) (hC3 : C3.length = b)
  (hC1v : value C1 = 2 ^ (b + 1)) (hC2v : value C2 + 2 ^ (b + 1) + 1 = 2 ^ (q - 1))
  (hC3v : value C3 + 2 = 2 ^ b)

include hq hC1 hC2 hC1v hC2v in
/-- A block of the first word raises a flag exactly when its digit fails the guard. -/
theorem flagsV_any (i : ℕ) :
    ((flagsV q V C1 C2 i).any id = true) ↔
      ¬ Guard ((2 : ℤ) ^ b) ((2 : ℤ) ^ (q - 1)) (value (field V (i * q) q)) := by
  simp only [flagsV, List.any_cons, List.any_nil, Bool.or_false, id, Bool.or_eq_true,
    decide_eq_true_eq, orderAfter_lt V C1 _ _ hC1, orderAfter_gt V C2 _ _ hC2, Guard]
  rw [← value_field_shift V (i * q) q (by omega)]
  have h2 : (2 : ℤ) * 2 ^ b = 2 ^ (b + 1) := by ring
  rw [h2]
  have e1 : ((2 : ℕ) ^ (b + 1) : ℤ) = (2 : ℤ) ^ (b + 1) := by push_cast; rfl
  have e2 : ((2 : ℕ) ^ (q - 1) : ℤ) = (2 : ℤ) ^ (q - 1) := by push_cast; rfl
  rw [hC1v]
  constructor
  · rintro (h | h)
    · intro hg; have := hg.1; omega
    · intro hg; have := hg.2; omega
  · intro hg
    by_contra hcon
    simp only [not_or, not_lt] at hcon
    exact hg ⟨by omega, by omega⟩

include hC3 hC3v in
/-- A block of the second word raises a flag exactly when its digit is the top value. -/
theorem flagsW_any (i : ℕ) :
    ((flagsW b W C3 i).any id = true) ↔ ¬ ((value (field W (i * b) b) : ℤ) < (2 : ℤ) ^ b - 1) := by
  simp only [flagsW, List.any_cons, List.any_nil, Bool.or_false, id, decide_eq_true_eq,
    orderAfter_gt W C3 _ _ hC3]
  have e : ((2 : ℕ) ^ b : ℤ) = (2 : ℤ) ^ b := by push_cast; rfl
  omega

include hV hW hq hC1 hC2 hC3 hC1v hC2v hC3v in
/-- Some flag is set exactly when the address is exceptional. -/
theorem flags_any (hVb : (value V : ℤ) < (2 * (2 : ℤ) ^ (q - 1)) ^ n)
    (hWb : (value W : ℤ) < ((2 : ℤ) ^ b) ^ n) :
    ((flagWordW q b n V W C1 C2 C3 n).any id = true) ↔
      ¬ earlyGood ((2 : ℤ) ^ b) ((2 : ℤ) ^ (q - 1)) n
        (⟨(value V : ℤ), by positivity, hVb⟩, ⟨(value W : ℤ), by positivity, hWb⟩) := by
  have hL : (2 : ℤ) * 2 ^ (q - 1) = 2 ^ q := by
    rw [← pow_succ']; congr 1; omega
  simp only [earlyGood, hL, digits_blocks V q n hV, digits_blocks W b n hW, blockValues,
    List.forall_mem_map, List.mem_range]
  rw [flagWordW_flatten, flagWordV_flatten, List.any_append, Bool.or_eq_true, List.any_flatten,
    List.any_map, List.any_flatten, List.any_map, List.any_eq_true, List.any_eq_true]
  simp only [Function.comp, List.mem_range]
  constructor
  · rintro (⟨i, hi, hf⟩ | ⟨i, hi, hf⟩)
    · intro hg; exact (flagsV_any q b V C1 C2 hq hC1 hC2 hC1v hC2v i).mp hf (hg.1 i hi)
    · intro hg; exact (flagsW_any b W C3 hC3 hC3v i).mp hf (hg.2 i hi)
  · intro hg
    by_contra hcon
    simp only [not_or, not_exists, not_and] at hcon
    apply hg
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · by_contra hb
      exact hcon.1 i hi ((flagsV_any q b V C1 C2 hq hC1 hC2 hC1v hC2v i).mpr hb)
    · by_contra hb
      exact hcon.2 i hi ((flagsW_any b W C3 hC3 hC3v i).mpr hb)

end Flags

end IntegerMultBounds.Compact.PowerTwo
