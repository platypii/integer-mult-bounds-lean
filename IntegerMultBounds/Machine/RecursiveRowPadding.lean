import IntegerMultBounds.Machine.Shared50RecursiveChildPermutation

/-! Exact row-major zero extension and cropping, retaining every prefix and
within-row suffix. These operations commute with the proved chunk transpose;
physical movement and generated span counts are separate charged subroutines. -/
namespace IntegerMultBounds.Machine.RecursiveRowPadding
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveInterchangeRows (pack rowLength)
variable {A R L : ℕ} {α : Type*}

def pad (R' : ℕ) (zero : α) (x : Fin (A*R*L) → α) : Fin (A*R'*L) → α := fun z =>
  let ar := finProdFinEquiv.symm (finProdFinEquiv.symm z).1
  let k := (finProdFinEquiv.symm z).2
  if h : ar.2.val < R then x (pack (pack ar.1 ⟨ar.2.val,h⟩) k) else zero

def crop {R' : ℕ} (h : R ≤ R') (x : Fin (A*R'*L) → α) : Fin (A*R*L) → α := fun z =>
  let ar := finProdFinEquiv.symm (finProdFinEquiv.symm z).1
  let k := (finProdFinEquiv.symm z).2
  x (pack (pack ar.1 ⟨ar.2.val,ar.2.isLt.trans_le h⟩) k)

def suffixMap (p : Fin L → Fin L) (x : Fin (A*R*L) → α) : Fin (A*R*L) → α := fun z =>
  let ar := (finProdFinEquiv.symm z).1
  x (pack ar (p (finProdFinEquiv.symm z).2))

theorem pad_entry (R' : ℕ) (zero : α) (x : Fin (A*R*L) → α)
    (a : Fin A) (r : Fin R') (k : Fin L) :
    pad R' zero x (pack (pack a r) k) =
      if h : r.val < R then x (pack (pack a ⟨r.val,h⟩) k) else zero := by
  simp [pad,pack]

theorem crop_entry {R' : ℕ} (h : R ≤ R') (x : Fin (A*R'*L) → α)
    (a : Fin A) (r : Fin R) (k : Fin L) :
    crop h x (pack (pack a r) k) = x (pack (pack a ⟨r.val,r.isLt.trans_le h⟩) k) := by
  simp [crop,pack]

theorem suffixMap_entry (p : Fin L → Fin L) (x : Fin (A*R*L) → α)
    (ar : Fin (A*R)) (k : Fin L) :
    suffixMap p x (pack ar k) = x (pack ar (p k)) := by simp [suffixMap,pack]

/-- Zero extension never changes any retained input cell. -/
theorem crop_pad {R' : ℕ} (h : R ≤ R') (zero : α) (x : Fin (A*R*L) → α) :
    crop h (pad R' zero x) = x := by
  funext z
  obtain ⟨⟨ar,k⟩,rfl⟩ := finProdFinEquiv.surjective z
  obtain ⟨⟨a,r⟩,rfl⟩ := finProdFinEquiv.surjective ar
  change crop h (pad R' zero x) (pack (pack a r) k) = x (pack (pack a r) k)
  rw [crop_entry,pad_entry,dite_eq_left r.isLt]

/-- Every suffix permutation preserves both valid rows and padded zero rows. -/
theorem pad_suffixMap (R' : ℕ) (zero : α) (p : Fin L → Fin L) (x : Fin (A*R*L) → α) :
    pad R' zero (suffixMap p x) = suffixMap p (pad R' zero x) := by
  funext z
  obtain ⟨⟨ar,k⟩,rfl⟩ := finProdFinEquiv.surjective z
  obtain ⟨⟨a,r⟩,rfl⟩ := finProdFinEquiv.surjective ar
  change pad R' zero (suffixMap p x) (pack (pack a r) k) = suffixMap p (pad R' zero x) (pack (pack a r) k)
  rw [pad_entry,suffixMap_entry,pad_entry]
  split <;> simp only [suffixMap_entry]

/-- Cropping also commutes with the same within-row permutation. -/
theorem crop_suffixMap {R' : ℕ} (h : R ≤ R') (p : Fin L → Fin L) (x : Fin (A*R'*L) → α) :
    crop h (suffixMap p x) = suffixMap p (crop h x) := by
  funext z
  obtain ⟨⟨ar,k⟩,rfl⟩ := finProdFinEquiv.surjective z
  obtain ⟨⟨a,r⟩,rfl⟩ := finProdFinEquiv.surjective ar
  change crop h (suffixMap p x) (pack (pack a r) k) = suffixMap p (crop h x) (pack (pack a r) k)
  rw [crop_entry,suffixMap_entry,suffixMap_entry,crop_entry]

/-- No original data is lost by a padded suffix permutation followed by crop. -/
theorem crop_permute_pad {R' : ℕ} (h : R ≤ R') (zero : α)
    (p : Fin L → Fin L) (x : Fin (A*R*L) → α) :
    crop h (suffixMap p (pad R' zero x)) = suffixMap p x := by
  rw [crop_suffixMap,crop_pad]

/-- The original seven-factor word, grouped by its literal prefix and row. -/
theorem volume_rows (v : Descriptor) :
    volume prime v = v.beforeRows*v.rows*rowLength prime v := by
  unfold volume rowLength
  ring

def rowView {v : Descriptor} (x : Fin (volume prime v) → α) :
    Fin (v.beforeRows*v.rows*rowLength prime v) → α :=
  fun z => x (Fin.cast (volume_rows v).symm z)

def rowIndex {v : Descriptor} (a : RecursiveInterchangeScaling.Address v) :
    Fin (v.beforeRows*v.rows*rowLength prime v) :=
  pack (pack a.beforeRows a.row)
    (Shared50RecursiveNodeRows.suffixPack (a.before,a.h,a.middle,a.d,a.after))

theorem suffix_value (v : Descriptor) (a : Fin v.beforeH) (h : Fin (prime^v.width))
    (m : Fin v.between) (d : Fin (prime^v.width)) (e : Fin v.afterD) :
    (Shared50RecursiveNodeRows.suffixPack (a,h,m,d,e)).val =
      (((a.val*prime^v.width+h.val)*v.between+m.val)*prime^v.width+d.val)*v.afterD+e.val := by
  simp only [Shared50RecursiveNodeRows.suffixPack,RecursiveInterchangeRows.suffixIndex,
    RecursiveInterchangeRows.pack_val]

theorem row_index {v : Descriptor} (a : RecursiveInterchangeScaling.Address v) :
    Fin.cast (volume_rows v) (RecursiveInterchangeScaling.index a) = rowIndex a := by
  apply Fin.ext
  change (RecursiveInterchangeScaling.index a).val =
    (pack (pack a.beforeRows a.row)
      (Shared50RecursiveNodeRows.suffixPack (a.before,a.h,a.middle,a.d,a.after))).val
  have hk := suffix_value v a.before a.h a.middle a.d a.after
  rw [RecursiveInterchangeScaling.index_val,RecursiveInterchangeRows.pack_val,
    RecursiveInterchangeRows.pack_val,hk]
  unfold RecursiveInterchangeLayout.index rowLength
  ring

theorem rowView_entry {v : Descriptor} (x : Fin (volume prime v) → α)
    (a : RecursiveInterchangeScaling.Address v) :
    rowView x (rowIndex a) = x (RecursiveInterchangeScaling.index a) := by
  rw [← row_index]
  simp only [rowView,Fin.cast_cast,Fin.cast_eq_self]

theorem rowView_injective (v : Descriptor) :
    Function.Injective (rowView (α := α) (v := v)) := by
  intro x y h
  funext z
  have hz := congrFun h (Fin.cast (volume_rows v) z)
  simpa only [rowView,Fin.cast_cast,Fin.cast_eq_self] using hz

/-- The proved physical chunk-transpose output is exactly a within-row map. -/
theorem rowView_transpose {v : Descriptor} (x : Fin (volume prime v) → α) :
    rowView (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x) =
      suffixMap Shared50RecursiveNodeRows.swapSuffix (rowView x) := by
  funext z
  obtain ⟨a,ha⟩ := RecursiveScalarIndex.scaling_surjective (Fin.cast (volume_rows v).symm z)
  have hz : rowIndex a = z := by
    rw [← row_index,ha]
    simp only [Fin.cast_cast,Fin.cast_eq_self]
  rw [← hz,rowView_entry]
  change _ = suffixMap Shared50RecursiveNodeRows.swapSuffix (rowView x)
    (pack (pack a.beforeRows a.row)
      (Shared50RecursiveNodeRows.suffixPack (a.before,a.h,a.middle,a.d,a.after)))
  rw [suffixMap_entry]
  have hs := Shared50RecursiveNodeRows.swapSuffix_pack (v := v) a.before a.h a.middle a.d a.after
  rw [hs]
  change _ = rowView x (rowIndex (Shared50RecursiveNodeTranspose.swapAddress a))
  rw [rowView_entry]
  have h := Shared50RecursiveNodeTranspose.transpose_all (by decide : 0 < 1)
    (one_dvd v.rows) x (Shared50RecursiveNodeTranspose.swapAddress a)
  simpa only [Shared50RecursiveNodeTranspose.swapAddress] using h

/-- Only the row field is enlarged; all suffix fields retain their addresses. -/
def withRows (v : Descriptor) (R' : ℕ) : Descriptor := {v with rows := R'}

/-- The physical padding wrapper's volume charge scales only with its row count. -/
theorem padded_volume_bound (v : Descriptor) (R' B : ℕ) (h : R' ≤ B*v.rows) :
    volume prime (withRows v R') ≤ B*volume prime v := by
  calc
    volume prime (withRows v R') = (v.beforeRows*rowLength prime v)*R' := by
      rw [volume_rows]
      change v.beforeRows*R'*rowLength prime v = _
      ring
    _ ≤ (v.beforeRows*rowLength prime v)*(B*v.rows) := Nat.mul_le_mul_left _ h
    _ = B*volume prime v := by rw [volume_rows]; ring


def padArray {v : Descriptor} (R' : ℕ) (zero : α) (x : Fin (volume prime v) → α) :
    Fin (volume prime (withRows v R')) → α :=
  fun z => pad R' zero (rowView x) (Fin.cast (volume_rows (withRows v R')) z)

def cropArray {v : Descriptor} {R' : ℕ} (h : v.rows ≤ R')
    (x : Fin (volume prime (withRows v R')) → α) : Fin (volume prime v) → α :=
  fun z => crop h (rowView x) (Fin.cast (volume_rows v) z)

theorem rowView_padArray {v : Descriptor} (R' : ℕ) (zero : α) (x : Fin (volume prime v) → α) :
    rowView (padArray R' zero x) = pad R' zero (rowView x) := by
  funext z
  change pad R' zero (rowView x) (Fin.cast _ (Fin.cast _ z)) = pad R' zero (rowView x) z
  exact congrArg (pad R' zero (rowView x)) (Fin.ext rfl)

theorem rowView_cropArray {v : Descriptor} {R' : ℕ} (h : v.rows ≤ R')
    (x : Fin (volume prime (withRows v R')) → α) :
    rowView (cropArray h x) = crop h (rowView x) := by
  funext z
  change crop h (rowView x) (Fin.cast _ (Fin.cast _ z)) = crop h (rowView x) z
  exact congrArg (crop h (rowView x)) (Fin.ext rfl)

/-- Exact descriptor-level transpose commutes with zero-filled row extension. -/
theorem padArray_transpose {v : Descriptor} (R' : ℕ) (zero : α) (x : Fin (volume prime v) → α) :
    padArray R' zero (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x) =
      Shared50RecursiveNodeRows.transpose (one_dvd R') (padArray R' zero x) := by
  apply rowView_injective (withRows v R')
  rw [rowView_padArray,rowView_transpose,rowView_transpose,rowView_padArray]
  exact pad_suffixMap R' zero Shared50RecursiveNodeRows.swapSuffix (rowView x)

/-- Removing the added rows recovers every original cell and spectator. -/
theorem cropArray_padArray {v : Descriptor} {R' : ℕ} (h : v.rows ≤ R')
    (zero : α) (x : Fin (volume prime v) → α) : cropArray h (padArray R' zero x) = x := by
  apply rowView_injective v
  rw [rowView_cropArray,rowView_padArray]
  exact crop_pad h zero (rowView x)

/-- This is the full semantic padding/interchange/unpadding wrapper. -/
theorem cropArray_transpose_padArray {v : Descriptor} {R' : ℕ} (h : v.rows ≤ R')
    (zero : α) (x : Fin (volume prime v) → α) :
    cropArray h (Shared50RecursiveNodeRows.transpose (one_dvd R') (padArray R' zero x)) =
      Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x := by
  rw [← padArray_transpose,cropArray_padArray]

end
end IntegerMultBounds.Machine.RecursiveRowPadding
