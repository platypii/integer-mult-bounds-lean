module

public import IntegerMultBounds.MathlibTM2.Routing.HaloIntervalLayout

/-! Byte slices aligned to fixed-width records are exactly encoded record
slices. The proof is structural and independent of the record representation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.FixedWidthSlice
open HaloIntervalLayout
variable {α β : Type}

theorem take_flatMap (encode : β → List α) (R : ℕ) (xs : List β) (hencode : ∀ x ∈ xs, (encode x).length = R) (n : ℕ) : (xs.flatMap encode).take (n*R) = (xs.take n).flatMap encode := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih =>
    have hx := hencode x (by simp)
    have ht : ∀ y ∈ xs, (encode y).length = R := fun y hy => hencode y (by simp [hy])
    cases n with
    | zero => simp
    | succ n =>
      simp only [List.flatMap_cons,List.take_succ_cons,Nat.succ_mul]
      rw [List.take_append,hx,List.take_of_length_le (by rw [hx]; omega)]
      simpa only [Nat.add_sub_cancel] using congrArg (encode x++·) (ih ht n)

theorem drop_flatMap (encode : β → List α) (R : ℕ) (xs : List β) (hencode : ∀ x ∈ xs, (encode x).length = R) (n : ℕ) : (xs.flatMap encode).drop (n*R) = (xs.drop n).flatMap encode := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih =>
    have hx := hencode x (by simp)
    have ht : ∀ y ∈ xs, (encode y).length = R := fun y hy => hencode y (by simp [hy])
    cases n with
    | zero => simp
    | succ n =>
      simp only [List.flatMap_cons,List.drop_succ_cons,Nat.succ_mul]
      rw [List.drop_append,hx,List.drop_eq_nil_of_le (by rw [hx]; omega)]
      simpa only [Nat.add_sub_cancel,List.nil_append] using ih ht n

theorem slice_flatMap (encode : β → List α) (R : ℕ) (xs : List β) (hencode : ∀ x ∈ xs, (encode x).length = R) (a b : ℕ) :
    slice (xs.flatMap encode) (a*R) (b*R) = (slice xs a b).flatMap encode := by
  unfold slice
  rw [drop_flatMap encode R xs hencode,←Nat.sub_mul,take_flatMap encode R (xs.drop a)
    (fun x hx => hencode x (List.mem_of_mem_drop hx))]

end IntegerMultBounds.MathlibTM2.Routing.FixedWidthSlice
