import IntegerMultBounds.Machine.RecursiveRowPadding

/-! Exact grouped words for the physical row padding and cropping streams.
Each prefix group contains its original row span followed by zero padding. -/
namespace IntegerMultBounds.Machine.RowPaddingWord
open RecursiveInterchangeRows (pack)
variable {A R L : ℕ} {α : Type*}

def spanIndex (a : Fin A) (k : Fin (R*L)) : Fin (A*R*L) :=
  Fin.cast (Nat.mul_assoc A R L).symm (pack a k)

def groups (x : Fin (A*R*L) → α) : List (List α) :=
  List.ofFn (fun a : Fin A => List.ofFn (fun k : Fin (R*L) => x (spanIndex a k)))

def padded (xs : List (List α)) (n : ℕ) (zero : α) :=
  xs.map (fun ys => ys ++ List.replicate n zero)

private theorem ofFn_pack {m n : ℕ} (f : Fin (m*n) → α) :
    List.ofFn f = (List.ofFn fun a : Fin m => List.ofFn fun b : Fin n => f (pack a b)).flatten := by
  simpa only [pack,finProdFinEquiv,Equiv.coe_fn_mk,Nat.add_comm,Nat.mul_comm] using List.ofFn_mul f

private theorem ofFn_cast {n m : ℕ} (he : n=m) (f : Fin m → α) :
    List.ofFn (fun i : Fin n => f (Fin.cast he i)) = List.ofFn f := by
  subst m
  rfl

/-- One original group per prefix, with the exact retained span length. -/
theorem group_length (x : Fin (A*R*L) → α) (xs : List α) (hx : xs ∈ groups x) : xs.length = R*L := by
  obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hx
  simp only [List.length_ofFn]

theorem groups_length (x : Fin (A*R*L) → α) : (groups x).length = A := by
  simp only [groups,List.length_ofFn]

/-- The physical grouped input word is literally the original flat array. -/
theorem groups_flatten (x : Fin (A*R*L) → α) : (groups x).flatten = List.ofFn x := by
  have hc := ofFn_cast (Nat.mul_assoc A R L).symm x
  rw [ofFn_pack] at hc
  exact hc

theorem spanIndex_pack (a : Fin A) (r : Fin R) (k : Fin L) :
    spanIndex a (pack r k) = pack (pack a r) k := by
  apply Fin.ext
  simp only [spanIndex,Fin.val_cast,RecursiveInterchangeRows.pack_val]
  ring

private theorem flatten_zero (n m : ℕ) (zero : α) :
    (List.replicate n (List.replicate m zero)).flatten = List.replicate (n*m) zero := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ,List.flatten_cons,ih,Nat.succ_mul]
    rw [← List.replicate_add,Nat.add_comm]

/-- Padding one prefix appends exactly the newly added complete rows. -/
theorem pad_group {R' : ℕ} (h : R ≤ R') (zero : α) (x : Fin (A*R*L) → α) (a : Fin A) :
    List.ofFn (fun k : Fin (R'*L) => RecursiveRowPadding.pad R' zero x (spanIndex a k)) =
      List.ofFn (fun k : Fin (R*L) => x (spanIndex a k)) ++ List.replicate ((R'-R)*L) zero := by
  rw [ofFn_pack,ofFn_pack]
  simp only [spanIndex_pack,RecursiveRowPadding.pad_entry]
  have hn : R+(R'-R)=R' := by omega
  rw [← ofFn_cast hn (fun r : Fin R' => List.ofFn (fun k : Fin L =>
    if hh : r.val < R then x (pack (pack a ⟨r.val,hh⟩) k) else zero))]
  rw [List.ofFn_add]
  simp only [Fin.val_cast,Fin.val_castLE,Fin.val_natAdd]
  have he : List.ofFn (fun r : Fin R => List.ofFn (fun k : Fin L =>
      if hh : r.val < R then x (pack (pack a ⟨r.val,hh⟩) k) else zero)) =
      List.ofFn (fun r : Fin R => List.ofFn (fun k : Fin L => x (pack (pack a r) k))) := by
    congr 1
    funext r
    simp only [dite_eq_left r.isLt]
  have hz : List.ofFn (fun r : Fin (R'-R) => List.ofFn (fun k : Fin L =>
      if hh : R+r.val < R then x (pack (pack a ⟨R+r.val,hh⟩) k) else zero)) =
      List.replicate (R'-R) (List.replicate L zero) := by
    have hf (r : Fin (R'-R)) : ¬R+r.val<R := by omega
    simp only [hf,dite_false,List.ofFn_const]
  rw [he,hz,List.flatten_append,flatten_zero]

/-- The exact word written by the grouped padding stream is the mathematical
row-major zero extension, for arbitrary numbers of prefixes and row length. -/
theorem ofFn_pad {R' : ℕ} (h : R ≤ R') (zero : α) (x : Fin (A*R*L) → α) :
    List.ofFn (RecursiveRowPadding.pad R' zero x) =
      (padded (groups x) ((R'-R)*L) zero).flatten := by
  rw [← groups_flatten (A := A) (R := R') (L := L) (RecursiveRowPadding.pad R' zero x)]
  unfold groups padded
  rw [List.map_ofFn]
  apply congrArg List.flatten
  congr 1
  funext a
  exact pad_group h zero x a

/-- A crop stream retains exactly the valid span from every prefix group. -/
def cropped (xs : List (List α)) (valid : ℕ) := xs.map (List.take valid)

theorem crop_padded_groups (zero : α) (x : Fin (A*R*L) → α) (extra : ℕ) :
    cropped (padded (groups x) extra zero) (R*L) = groups x := by
  unfold cropped padded
  rw [List.map_map]
  calc
    _ = (groups x).map id := by
      apply List.map_congr_left
      intro ys hy
      rw [← group_length x ys hy]
      simp
    _ = _ := List.map_id _

/-- After valid-span movement, the appended padding is discarded and the
original flat word is recovered; its values may include zero symbols. -/
theorem crop_padded_word (zero : α) (x : Fin (A*R*L) → α) (extra : ℕ) :
    (cropped (padded (groups x) extra zero) (R*L)).flatten = List.ofFn x := by
  rw [crop_padded_groups,groups_flatten]

theorem ofFn_crop_pad {R' : ℕ} (h : R ≤ R') (zero : α) (x : Fin (A*R*L) → α) :
    List.ofFn (RecursiveRowPadding.crop h (RecursiveRowPadding.pad R' zero x)) = (groups x).flatten := by
  rw [RecursiveRowPadding.crop_pad,groups_flatten]

section Descriptor
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveInterchangeRows (rowLength)
variable {v : Descriptor}

theorem rowView_word (x : Fin (volume prime v) → α) :
    List.ofFn (RecursiveRowPadding.rowView x) = List.ofFn x :=
  ofFn_cast (RecursiveRowPadding.volume_rows v).symm x

/-- Descriptor-level input is the exact same prefix-grouped physical word. -/
theorem descriptor_groups (x : Fin (volume prime v) → α) :
    (groups (RecursiveRowPadding.rowView x)).flatten = List.ofFn x := by
  rw [groups_flatten,rowView_word]

/-- The stream padding contract is exactly the full descriptor zero extension. -/
theorem padArray_word {R' : ℕ} (h : v.rows ≤ R') (zero : α) (x : Fin (volume prime v) → α) :
    List.ofFn (RecursiveRowPadding.padArray R' zero x) =
      (padded (groups (RecursiveRowPadding.rowView x)) ((R'-v.rows)*rowLength prime v) zero).flatten := by
  rw [← rowView_word (RecursiveRowPadding.padArray R' zero x),RecursiveRowPadding.rowView_padArray]
  exact ofFn_pad h zero (RecursiveRowPadding.rowView x)

/-- The valid-span crop word after the actual full transpose is the original
full transpose word, preserving every prefix, row and suffix spectator. -/
theorem cropArray_transpose_word {R' : ℕ} (h : v.rows ≤ R') (zero : α)
    (x : Fin (volume prime v) → α) :
    List.ofFn (RecursiveRowPadding.cropArray h
      (Shared50RecursiveNodeRows.transpose (one_dvd R') (RecursiveRowPadding.padArray R' zero x))) =
      List.ofFn (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x) := by
  rw [RecursiveRowPadding.cropArray_transpose_padArray]

end Descriptor

end IntegerMultBounds.Machine.RowPaddingWord
