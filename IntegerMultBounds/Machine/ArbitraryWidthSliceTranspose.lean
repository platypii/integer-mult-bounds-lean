import IntegerMultBounds.Machine.ArbitraryWidthPieces
import IntegerMultBounds.Machine.Shared50RecursiveChildPermutation

/-! Literal slice transposes exchange the same consecutive digit window in
the original full-width scalar fields, retaining all outside coordinates. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthSliceTranspose
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open FlatCoordinateLayout (rank)
variable {q : ℕ} [NeZero q]

/-- Existing rank is the most-significant-first weighted digit sum. -/
theorem rank_sum {n : ℕ} (x : Fin n → ZMod q) :
    (rank x).val = ∑ i : Fin n, (x i).val*q^(n-1-i.val) := by
  unfold rank
  rw [finFunctionFinEquiv_apply]
  have he := Equiv.sum_comp Fin.revPerm (fun i : Fin n => (x i).val*q^(n-1-i.val))
  simp only [FlatCoordinateLayout.finEquiv_symm_val]
  calc
    _ = ∑ i : Fin n, (x i.rev).val*q^(n-1-i.rev.val) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Fin.val_rev]
      congr 2
      have := i.isLt
      omega
    _ = _ := by simpa only [Fin.revPerm_apply] using he

/-- Concatenation of digit vectors is the existing concatenation of ranks. -/
theorem rank_append {a b : ℕ} (x : Fin a → ZMod q) (y : Fin b → ZMod q) :
    (rank (Fin.addCases x y)).val = (rank x).val*q^b+(rank y).val := by
  rw [rank_sum,Fin.sum_univ_add,rank_sum,rank_sum,Finset.sum_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    simp only [Fin.addCases_left,Fin.val_castAdd]
    have he : a+b-1-i.val = (a-1-i.val)+b := by have := i.isLt; omega
    rw [he,pow_add]
    ring
  · apply Finset.sum_congr rfl
    intro i _
    simp only [Fin.addCases_right,Fin.val_natAdd]
    congr 2
    omega

def preDigits {n : ℕ} (offset width : ℕ) (hfit : offset+width ≤ n) (x : Fin n → ZMod q) :
    Fin offset → ZMod q := fun i => x ⟨i.val,by have := i.isLt; omega⟩
def middle {n : ℕ} (offset width : ℕ) (hfit : offset+width ≤ n) (x : Fin n → ZMod q) :
    Fin width → ZMod q := fun i => x ⟨offset+i.val,by have := i.isLt; omega⟩
def suffix {n : ℕ} (offset width : ℕ) (_hfit : offset+width ≤ n) (x : Fin n → ZMod q) :
    Fin (n-offset-width) → ZMod q := fun i => x ⟨offset+width+i.val,by have := i.isLt; omega⟩

private theorem rank_cast {n m : ℕ} (he : n=m) (x : Fin m → ZMod q) :
    (rank (fun i : Fin n => x (Fin.cast he i))).val = (rank x).val := by
  subst m
  rfl

/-- Prefix, selected window and suffix are literal intervals of the existing
most-significant-first coordinate vector. -/
theorem rank_split {n : ℕ} (offset width : ℕ) (hfit : offset+width ≤ n) (x : Fin n → ZMod q) :
    (rank x).val = ((rank (preDigits offset width hfit x)).val*q^width+
      (rank (middle offset width hfit x)).val)*q^(n-offset-width)+
      (rank (suffix offset width hfit x)).val := by
  have hn : offset+(width+(n-offset-width))=n := by omega
  have hf : Fin.addCases (preDigits offset width hfit x)
      (Fin.addCases (middle offset width hfit x) (suffix offset width hfit x)) =
      fun i => x (Fin.cast hn i) := by
    funext i
    induction i using Fin.addCases with
    | left i =>
      simp only [Fin.addCases_left,preDigits]
      congr 1
    | right i =>
      induction i using Fin.addCases with
      | left i =>
        simp only [Fin.addCases_right,Fin.addCases_left,middle]
        congr 1
      | right i =>
        simp only [Fin.addCases_right,suffix]
        congr 1
        apply Fin.ext
        simp only [Fin.val_cast,Fin.val_natAdd]
        omega
  rw [← rank_cast hn x,← hf,rank_append,rank_append,pow_add]
  ring

/-- Swapping one window replaces its rank and retains both surrounding ranks. -/
theorem rank_window {n : ℕ} (offset width : ℕ) (hfit : offset+width ≤ n)
    (h d : Fin n → ZMod q) :
    (rank (fun z => (ArbitraryWidthPieces.swapWindow offset width (fun z => (h z,d z)) z).1)).val =
      ((rank (preDigits offset width hfit h)).val*q^width+(rank (middle offset width hfit d)).val)*
        q^(n-offset-width)+(rank (suffix offset width hfit h)).val := by
  rw [rank_split offset width hfit]
  have hp : preDigits offset width hfit (fun z =>
      (ArbitraryWidthPieces.swapWindow offset width (fun z => (h z,d z)) z).1) = preDigits offset width hfit h := by
    funext i
    simp only [preDigits,ArbitraryWidthPieces.swapWindow]
    rw [ite_eq_right (by have := i.isLt; omega)]
  have hm : middle offset width hfit (fun z =>
      (ArbitraryWidthPieces.swapWindow offset width (fun z => (h z,d z)) z).1) = middle offset width hfit d := by
    funext i
    simp only [middle,ArbitraryWidthPieces.swapWindow]
    rw [ite_eq_left (by have := i.isLt; constructor <;> omega)]
    rfl
  have hs : suffix offset width hfit (fun z =>
      (ArbitraryWidthPieces.swapWindow offset width (fun z => (h z,d z)) z).1) = suffix offset width hfit h := by
    funext i
    simp only [suffix,ArbitraryWidthPieces.swapWindow]
    rw [ite_eq_right (by omega)]
  rw [hp,hm,hs]

theorem rank_window_d {n : ℕ} (offset width : ℕ) (hfit : offset+width ≤ n)
    (h d : Fin n → ZMod q) :
    (rank (fun z => (ArbitraryWidthPieces.swapWindow offset width (fun z => (h z,d z)) z).2)).val =
      ((rank (preDigits offset width hfit d)).val*q^width+(rank (middle offset width hfit h)).val)*
        q^(n-offset-width)+(rank (suffix offset width hfit d)).val := by
  have he : (fun z => (ArbitraryWidthPieces.swapWindow offset width (fun z => (h z,d z)) z).2) =
      fun z => (ArbitraryWidthPieces.swapWindow offset width (fun z => (d z,h z)) z).1 := by
    funext z
    unfold ArbitraryWidthPieces.swapWindow
    split_ifs <;> rfl
  rw [he]
  exact rank_window offset width hfit d h

section Physical
local instance : NeZero prime := ⟨ne_of_gt Shared50ModularControl.prime_prime.pos⟩
variable {v : Descriptor}

/-- Every selected slice field is packed in the original spectator order. -/
def sliceAddress (offset width : ℕ) (hfit : offset+width ≤ v.width)
    (a : RecursiveInterchangeScaling.Address v) :
    RecursiveInterchangeScaling.Address (ArbitraryWidthPieces.slice prime v offset width) where
  beforeRows := a.beforeRows
  row := a.row
  before := finProdFinEquiv (a.before,rank (preDigits offset width hfit (FlatCoordinateLayout.coordinates a.h)))
  h := rank (middle offset width hfit (FlatCoordinateLayout.coordinates a.h))
  middle := finProdFinEquiv (finProdFinEquiv
    (rank (suffix offset width hfit (FlatCoordinateLayout.coordinates a.h)),a.middle),
    rank (preDigits offset width hfit (FlatCoordinateLayout.coordinates a.d)))
  d := rank (middle offset width hfit (FlatCoordinateLayout.coordinates a.d))
  after := finProdFinEquiv (rank (suffix offset width hfit (FlatCoordinateLayout.coordinates a.d)),a.after)

/-- No movement is performed by reinterpreting the selected power-width slice. -/
theorem slice_index (offset width : ℕ) (hfit : offset+width ≤ v.width)
    (a : RecursiveInterchangeScaling.Address v) :
    Fin.cast (ArbitraryWidthPieces.slice_volume prime v offset width hfit)
      (RecursiveInterchangeScaling.index (sliceAddress offset width hfit a)) =
      RecursiveInterchangeScaling.index a := by
  apply Fin.ext
  rw [Fin.val_cast,RecursiveInterchangeScaling.index_val,RecursiveInterchangeScaling.index_val]
  have hh := rank_split offset width hfit (FlatCoordinateLayout.coordinates a.h)
  have hd := rank_split offset width hfit (FlatCoordinateLayout.coordinates a.d)
  rw [FlatCoordinateLayout.rank_coordinates (Q := prime) (d := v.width) a.h] at hh
  rw [FlatCoordinateLayout.rank_coordinates (Q := prime) (d := v.width) a.d] at hd
  simp only [RecursiveInterchangeLayout.index,ArbitraryWidthPieces.slice,sliceAddress,
    finProdFinEquiv,Equiv.coe_fn_mk]
  rw [hh,hd]
  have hp : prime^v.width = prime^offset*prime^width*prime^(v.width-offset-width) := by
    rw [← pow_add,← pow_add]
    congr 1
    omega
  rw [hp]
  ring

/-- Full scalar address after exactly the named window is exchanged. -/
def windowAddress (offset width : ℕ) (a : RecursiveInterchangeScaling.Address v) :
    RecursiveInterchangeScaling.Address v :=
  let out := ArbitraryWidthPieces.swapWindow offset width
    (fun z => (FlatCoordinateLayout.coordinates a.h z,FlatCoordinateLayout.coordinates a.d z))
  {a with h := rank (fun z => (out z).1),d := rank (fun z => (out z).2)}

/-- Swapping the slice's two selected fields is the same parent flat cell as
exchanging that digit interval, including all unchanged spectator factors. -/
theorem swapped_index (offset width : ℕ) (hfit : offset+width ≤ v.width)
    (a : RecursiveInterchangeScaling.Address v) :
    Fin.cast (ArbitraryWidthPieces.slice_volume prime v offset width hfit)
      (RecursiveInterchangeScaling.index (Shared50RecursiveNodeTranspose.swapAddress
        (sliceAddress offset width hfit a))) =
      RecursiveInterchangeScaling.index (windowAddress offset width a) := by
  apply Fin.ext
  rw [Fin.val_cast,RecursiveInterchangeScaling.index_val,RecursiveInterchangeScaling.index_val]
  have hh := rank_window offset width hfit (FlatCoordinateLayout.coordinates a.h) (FlatCoordinateLayout.coordinates a.d)
  have hd := rank_window_d offset width hfit (FlatCoordinateLayout.coordinates a.h) (FlatCoordinateLayout.coordinates a.d)
  simp only [RecursiveInterchangeLayout.index,ArbitraryWidthPieces.slice,sliceAddress,
    Shared50RecursiveNodeTranspose.swapAddress,windowAddress,finProdFinEquiv,Equiv.coe_fn_mk]
  rw [hh,hd]
  have hp : prime^v.width = prime^offset*prime^width*prime^(v.width-offset-width) := by
    rw [← pow_add,← pow_add]
    congr 1
    omega
  rw [hp]
  ring

/-- Selected power-width input is the exact original physical word. -/
def toSlice {α : Type*} (offset width : ℕ) (hfit : offset+width ≤ v.width)
    (x : Fin (volume prime v) → α) :
    Fin (volume prime (ArbitraryWidthPieces.slice prime v offset width)) → α :=
  fun z => x (Fin.cast (ArbitraryWidthPieces.slice_volume prime v offset width hfit) z)

/-- The actual power-width transpose returned through the same-volume slice. -/
def array {α : Type*} (offset width : ℕ) (hfit : offset+width ≤ v.width)
    (x : Fin (volume prime v) → α) : Fin (volume prime v) → α := fun z =>
  Shared50RecursiveNodeRows.transpose (one_dvd _) (toSlice offset width hfit x)
    (Fin.cast (ArbitraryWidthPieces.slice_volume prime v offset width hfit).symm z)

/-- Complete slice execution has the original selected-window semantics at
all original addresses, without discarding spectator fields or row positions. -/
theorem array_entry {α : Type*} (offset width : ℕ) (hfit : offset+width ≤ v.width)
    (x : Fin (volume prime v) → α) (a : RecursiveInterchangeScaling.Address v) :
    array offset width hfit x (RecursiveInterchangeScaling.index (windowAddress offset width a)) =
      x (RecursiveInterchangeScaling.index a) := by
  rw [← swapped_index offset width hfit a]
  unfold array
  rw [Fin.cast_cast,Fin.cast_eq_self]
  rw [Shared50RecursiveNodeTranspose.transpose_all (by decide : 0 < 1)]
  change x (Fin.cast (ArbitraryWidthPieces.slice_volume prime v offset width hfit)
    (RecursiveInterchangeScaling.index (sliceAddress offset width hfit a))) = _
  rw [slice_index]

theorem toSlice_word {α : Type*} (offset width : ℕ) (hfit : offset+width ≤ v.width)
    (x : Fin (volume prime v) → α) : List.ofFn (toSlice offset width hfit x) = List.ofFn x :=
  (List.ofFn_congr (ArbitraryWidthPieces.slice_volume prime v offset width hfit).symm x).symm

theorem return_word {α : Type*} (offset width : ℕ) (hfit : offset+width ≤ v.width)
    (x : Fin (volume prime v) → α) :
    List.ofFn (Shared50RecursiveNodeRows.transpose (one_dvd _) (toSlice offset width hfit x)) =
      List.ofFn (array offset width hfit x) :=
  List.ofFn_congr (ArbitraryWidthPieces.slice_volume prime v offset width hfit) _

/-- Entry and return agree as actual four-symbol source tapes. -/
theorem toSlice_source (offset width : ℕ) (hfit : offset+width ≤ v.width)
    (x : Fin (volume prime v) → Fin 4) :
    RecursiveShiftRoleBank.source (toSlice offset width hfit x) = RecursiveShiftRoleBank.source x := by
  change FlatRepeatedControlNormalize.encoded (putWord (fun _ => blank) 0
    (List.ofFn (toSlice offset width hfit x))) = _
  rw [toSlice_word]
  rfl

theorem return_source (offset width : ℕ) (hfit : offset+width ≤ v.width)
    (x : Fin (volume prime v) → Fin 4) :
    RecursiveShiftRoleBank.source (Shared50RecursiveNodeRows.transpose (one_dvd _) (toSlice offset width hfit x)) =
      RecursiveShiftRoleBank.source (array offset width hfit x) := by
  change FlatRepeatedControlNormalize.encoded (putWord (fun _ => blank) 0
    (List.ofFn (Shared50RecursiveNodeRows.transpose (one_dvd _) (toSlice offset width hfit x)))) = _
  rw [return_word]
  rfl

/-- Physical binary encoding commutes with the full selected-window permutation. -/
theorem array_encoded (offset width : ℕ) (hfit : offset+width ≤ v.width)
    (x : Fin (volume prime v) → ZMod 2) :
    array offset width hfit (Shared50RecursiveNodeSemantics.encoded x) =
      Shared50RecursiveNodeSemantics.encoded (array offset width hfit x) := rfl

/-- The output rank is exactly the scalar window exchange named by the
arbitrary-width partition, rather than a separate replacement permutation. -/
theorem window_coordinates (offset width : ℕ) (a : RecursiveInterchangeScaling.Address v) :
    (fun z => (FlatCoordinateLayout.coordinates (windowAddress offset width a).h z,
      FlatCoordinateLayout.coordinates (windowAddress offset width a).d z)) =
      ArbitraryWidthPieces.swapWindow offset width
        (fun z => (FlatCoordinateLayout.coordinates a.h z,FlatCoordinateLayout.coordinates a.d z)) := by
  simp only [windowAddress,FlatCoordinateLayout.coordinates_rank]

theorem window_spectators (offset width : ℕ) (a : RecursiveInterchangeScaling.Address v) :
    (windowAddress offset width a).beforeRows = a.beforeRows ∧
    (windowAddress offset width a).row = a.row ∧
    (windowAddress offset width a).before = a.before ∧
    (windowAddress offset width a).middle = a.middle ∧
    (windowAddress offset width a).after = a.after := ⟨rfl,rfl,rfl,rfl,rfl⟩

end Physical

end
end IntegerMultBounds.Machine.ArbitraryWidthSliceTranspose
