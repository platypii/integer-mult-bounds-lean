module

public import IntegerMultBounds.MathlibTM2.Routing.FixedWidthSlice

/-! Decode a flat offset into an arbitrary list of uniform records. Structural
list recursion shares the proof across all tensor sizes and spectator widths. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.FixedWidthIndex
variable {α β : Type}

theorem getElem?_flatMap (encode : β → List α) (R : ℕ) (hR : 0 < R) (xs : List β)
    (hencode : ∀ x ∈ xs, (encode x).length = R) (i : ℕ) :
    (xs.flatMap encode)[i]? = (xs[i/R]?).bind (fun x => (encode x)[i%R]?) := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
    have hx := hencode x (by simp)
    have ht : ∀ y ∈ xs, (encode y).length = R := fun y hy => hencode y (by simp [hy])
    by_cases hi : i < R
    · rw [List.flatMap_cons,List.getElem?_append_left (by rw [hx]; exact hi),
        Nat.div_eq_of_lt hi,Nat.mod_eq_of_lt hi]
      rfl
    · have hge : R ≤ i := by omega
      rw [List.flatMap_cons,List.getElem?_append_right (by rw [hx]; exact hge),hx,ih ht,
        Nat.div_eq_sub_div hR hge,List.getElem?_cons_succ,Nat.mod_eq_sub_mod hge]

end IntegerMultBounds.MathlibTM2.Routing.FixedWidthIndex
