import Mathlib.Data.List.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Executable stable least-significant-bit radix sorting of arbitrary records.
Each pass is exactly the false filter followed by the true filter. The theorems
here describe lists and the record volume traversed by the passes; they do not
claim a tape implementation or charge list operations as machine steps. -/

namespace IntegerMultBounds.Machine.RadixSort

variable {α : Type*}

/-- A stable binary partition, with the false bucket first. -/
def pass (bit : α → Bool) (xs : List α) : List α :=
  xs.filter (fun x => !(bit x)) ++ xs.filter bit

/-- Process bit zero first; bit `k` is the next more significant bit. -/
def sort (bit : α → ℕ → Bool) : ℕ → List α → List α
  | 0, xs => xs
  | k + 1, xs => pass (fun x => bit x k) (sort bit k xs)

/-- The natural-number value of the low `k` bits of a record's key. -/
def keyValue (bit : α → ℕ → Bool) : ℕ → α → ℕ
  | 0, _ => 0
  | k + 1, x => keyValue bit k x + if bit x k then 2 ^ k else 0

theorem pass_perm (bit : α → Bool) (xs : List α) : (pass bit xs).Perm xs := by
  simpa [pass] using List.filter_append_perm (fun x => !(bit x)) xs

theorem sort_perm (bit : α → ℕ → Bool) (k : ℕ) (xs : List α) :
    (sort bit k xs).Perm xs := by
  induction k with
  | zero => exact List.Perm.refl _
  | succ k ih => exact (pass_perm _ _).trans ih

@[simp] theorem pass_length (bit : α → Bool) (xs : List α) :
    (pass bit xs).length = xs.length := (pass_perm bit xs).length_eq

@[simp] theorem sort_length (bit : α → ℕ → Bool) (k : ℕ) (xs : List α) :
    (sort bit k xs).length = xs.length := (sort_perm bit k xs).length_eq

theorem keyValue_lt (bit : α → ℕ → Bool) (k : ℕ) (x : α) :
    keyValue bit k x < 2 ^ k := by
  induction k with
  | zero => simp [keyValue]
  | succ k ih =>
    simp only [keyValue, pow_succ]
    cases bit x k <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- Equality of represented values is precisely equality of the processed bits. -/
theorem keyValue_eq_iff (bit : α → ℕ → Bool) (k : ℕ) (x y : α) :
    keyValue bit k x = keyValue bit k y ↔ ∀ i < k, bit x i = bit y i := by
  induction k with
  | zero => simp [keyValue]
  | succ k ih =>
    have hx := keyValue_lt bit k x
    have hy := keyValue_lt bit k y
    have hstep : keyValue bit (k + 1) x = keyValue bit (k + 1) y ↔
        keyValue bit k x = keyValue bit k y ∧ bit x k = bit y k := by
      cases hbx : bit x k <;> cases hby : bit y k <;>
        simp only [keyValue, hbx, hby, Bool.false_eq_true, Bool.true_eq_false,
          ↓reduceIte, Nat.add_zero, and_true, and_false, iff_false, Nat.add_right_cancel_iff] <;> omega
    rw [hstep, ih]
    constructor
    · rintro ⟨h, hk⟩ i hi
      by_cases heq : i = k
      · simpa [heq] using hk
      · exact h i (by omega)
    · intro h
      exact ⟨fun i hi => h i (by omega), h k (by omega)⟩

/-- A pass preserves the order of a selected subsequence whenever the selected
records all have the same routing bit. No equality on records is required. -/
theorem filter_pass (bit p : α → Bool) (b : Bool) (xs : List α)
    (h : ∀ x, p x = true → bit x = b) :
    (pass bit xs).filter p = xs.filter p := by
  have hf : ∀ x, (p x && !(bit x)) = if b then false else p x := by
    intro x
    cases hp : p x with
    | false => simp
    | true => simp [h x hp]
  have ht : ∀ x, (p x && bit x) = if b then p x else false := by
    intro x
    cases hp : p x with
    | false => simp
    | true => simp [h x hp]
  simp only [pass, List.filter_append, List.filter_filter]
  simp_rw [hf, ht]
  cases b <;> simp

/-- Every subsequence with one fixed processed key stays in its original order.
This includes arbitrary payloads and duplicate records. -/
theorem filter_sort (bit : α → ℕ → Bool) (p : α → Bool) (target : ℕ → Bool)
    (k : ℕ) (xs : List α)
    (h : ∀ x, p x = true → ∀ i < k, bit x i = target i) :
    (sort bit k xs).filter p = xs.filter p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [sort, filter_pass _ _ (target k) _ (fun x hx => h x hx k (by omega))]
    exact ih (fun x hx i hi => h x hx i (by omega))

/-- Filtering by any one complete numeric key yields the identical list before
and after sorting, so equal-key payload order is preserved exactly. -/
theorem filter_sort_key (bit : α → ℕ → Bool) (k : ℕ) (xs : List α) (x : α) :
    (sort bit k xs).filter (fun y => decide (keyValue bit k y = keyValue bit k x)) =
      xs.filter (fun y => decide (keyValue bit k y = keyValue bit k x)) := by
  apply filter_sort bit _ (bit x) k xs
  intro y hy
  exact (keyValue_eq_iff bit k y x).mp (by simpa using hy)

/-- One stable partition extends sortedness from the low `k` bits to `k + 1`. -/
theorem pass_pairwise (bit : α → ℕ → Bool) (k : ℕ) (xs : List α)
    (hs : xs.Pairwise (fun x y => keyValue bit k x ≤ keyValue bit k y)) :
    (pass (fun x => bit x k) xs).Pairwise
      (fun x y => keyValue bit (k + 1) x ≤ keyValue bit (k + 1) y) := by
  apply List.pairwise_append.mpr
  refine ⟨?_, ?_, ?_⟩
  · apply (hs.filter (fun x => !(bit x k))).imp_of_mem
    intro x y hx hy hxy
    have hx' : bit x k = false := by simpa using (List.mem_filter.mp hx).2
    have hy' : bit y k = false := by simpa using (List.mem_filter.mp hy).2
    simpa [keyValue, hx', hy'] using hxy
  · apply (hs.filter (fun x => bit x k)).imp_of_mem
    intro x y hx hy hxy
    have hx' := (List.mem_filter.mp hx).2
    have hy' := (List.mem_filter.mp hy).2
    simpa [keyValue, hx', hy'] using Nat.add_le_add_right hxy (2 ^ k)
  · intro x hx y hy
    have hx' : bit x k = false := by simpa using (List.mem_filter.mp hx).2
    have hy' := (List.mem_filter.mp hy).2
    have hbound := keyValue_lt bit k x
    simp only [keyValue, hx', Bool.false_eq_true, ↓reduceIte, Nat.add_zero, hy']
    omega

/-- After `k` passes the records are sorted by all `k` key bits. -/
theorem sort_pairwise (bit : α → ℕ → Bool) (k : ℕ) (xs : List α) :
    (sort bit k xs).Pairwise (fun x y => keyValue bit k x ≤ keyValue bit k y) := by
  induction k with
  | zero =>
    induction xs with
    | nil => exact .nil
    | cons x xs ih => exact .cons (by simp [keyValue]) ih
  | succ k ih => exact pass_pairwise bit k _ ih

/-- Total encoded record volume, allowing variable-sized payloads. -/
def volume (weight : α → ℕ) (xs : List α) : ℕ := (xs.map weight).sum

@[simp] theorem pass_volume (bit : α → Bool) (weight : α → ℕ) (xs : List α) :
    volume weight (pass bit xs) = volume weight xs :=
  ((pass_perm bit xs).map weight).sum_eq

@[simp] theorem sort_volume (bit : α → ℕ → Bool) (weight : α → ℕ)
    (k : ℕ) (xs : List α) : volume weight (sort bit k xs) = volume weight xs :=
  ((sort_perm bit k xs).map weight).sum_eq

/-- Sum of input volumes of the actual successive stable-partition passes.
This quantity does not include tape positioning, selection, or encoding costs. -/
def traversedVolume (bit : α → ℕ → Bool) (weight : α → ℕ) : ℕ → List α → ℕ
  | 0, _ => 0
  | k + 1, xs => traversedVolume bit weight k xs + volume weight (sort bit k xs)

theorem traversedVolume_eq (bit : α → ℕ → Bool) (weight : α → ℕ)
    (k : ℕ) (xs : List α) :
    traversedVolume bit weight k xs = k * volume weight xs := by
  induction k with
  | zero => simp [traversedVolume]
  | succ k ih => simp [traversedVolume, ih, Nat.succ_mul]

/-- A uniform upper bound on encoded record sizes gives the usual volume bound. -/
theorem volume_le (weight : α → ℕ) (xs : List α) (width : ℕ)
    (h : ∀ x ∈ xs, weight x ≤ width) : volume weight xs ≤ xs.length * width := by
  induction xs with
  | nil => simp [volume]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [volume, List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul] at *
    omega

/-- An explicit bound for `k` partition traversals of bounded-width records. -/
theorem traversedVolume_le (bit : α → ℕ → Bool) (weight : α → ℕ)
    (k : ℕ) (xs : List α) (width : ℕ) (h : ∀ x ∈ xs, weight x ≤ width) :
    traversedVolume bit weight k xs ≤ k * (xs.length * width) := by
  rw [traversedVolume_eq]
  exact Nat.mul_le_mul_left k (volume_le weight xs width h)

/-- Each record is routed once per pass, including empty inputs and zero-bit keys. -/
theorem traversedVolume_recordCount (bit : α → ℕ → Bool) (k : ℕ) (xs : List α) :
    traversedVolume bit (fun _ => 1) k xs = k * xs.length := by
  rw [traversedVolume_eq]
  congr 1
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [volume, List.map_cons, List.sum_cons, List.length_cons] at *
    omega

end IntegerMultBounds.Machine.RadixSort
