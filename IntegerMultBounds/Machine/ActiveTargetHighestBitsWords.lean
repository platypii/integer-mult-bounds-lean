import IntegerMultBounds.Machine.ActiveTargetHighestBits
import IntegerMultBounds.Compact.ActiveTargetSubsegmentWords

/-! Literal bit-word semantics of the one-bit coordinate split. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestBitsWords
noncomputable section
open ActiveTargetHighestBits
open BinaryAddressTableData
open Compact.ActiveTargetSubsegmentWords

def bool (x : Fin 2) : Bool := decide (x.val=1)
theorem bool_value (x : Fin 2) : Counter.value [bool x]=x.val := by fin_cases x <;> rfl

theorem bool_xor (x y : Fin 2) : bool (ActiveTargetHighestLaterValue.xorBit x y)=xor (bool x) (bool y) := by
  fin_cases x <;> fin_cases y <;> rfl

theorem row_join (width pos : ℕ) (h : pos<width) (x : Parts width pos) :
    row width (join width pos h x).val=
      row pos x.2.val++[bool x.1.2]++row (width-pos-1) x.1.1.val := by
  apply CountedPackedGuarded.word_eq_of_length_value
  · simp only [row_length,List.length_append,List.length_singleton]
    omega
  · rw [row_rank _ _ (join width pos h x).isLt,ColumnTransducer.value_append,
      ColumnTransducer.value_append,row_rank _ _ x.2.isLt,bool_value,
      row_rank _ _ x.1.1.isLt]
    simp only [List.length_append,row_length,List.length_singleton,join_val,pow_add,pow_one]
    ring

theorem row_split (width pos : ℕ) (h : pos<width) (x : Fin (2^width)) :
    row width x.val=row pos (split width pos h x).2.val++[bool (split width pos h x).1.2]++
      row (width-pos-1) (split width pos h x).1.1.val := by
  conv_lhs => rw [←join_split width pos h x]
  exact row_join width pos h _

theorem row_zero (i : ℕ) : row 0 i=[] := List.eq_nil_of_length_eq_zero (row_length 0 i)

theorem row_toggle_low (width : ℕ) (h : 0<width) (source : Fin 2) (x : Fin (2^width)) :
    row width (toggle width 0 h source x).val=highest (bool source) (row width x.val) := by
  rw [row_split width 0 h (toggle width 0 h source x),split_toggle,row_split width 0 h x]
  simp only [row_zero,List.nil_append,List.singleton_append,bool_xor,highest]

theorem highest_append (b : Bool) (xs ys : List Bool) (hx : xs≠[]) :
    highest b (xs++ys)=highest b xs++ys := by
  cases xs with
  | nil => exact (hx rfl).elim
  | cons x xs => rfl

theorem source_bit (width pos : ℕ) (h : pos<width) (x : Fin (2^width)) :
    bool (split width pos h x).1.2=Nat.testBit x.val pos := by
  rw [bool,source_value,Nat.testBit_eq_decide_div_mod_eq]

end
end IntegerMultBounds.Machine.ActiveTargetHighestBitsWords
