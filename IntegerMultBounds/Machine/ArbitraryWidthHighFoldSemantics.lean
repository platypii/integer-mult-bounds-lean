import IntegerMultBounds.Machine.ArbitraryWidthHighPrefix
import IntegerMultBounds.Machine.Shared50RecursiveNodeTranspose

/-! Folding the three adjacent spectator factors is a cast of the same literal
serialized word. It commutes with the complete H/D transpose. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighFoldSemantics
noncomputable section
open Networks
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveInterchangeScaling (Address)
open Shared50ModularControl (prime)

def folded (v : Descriptor) : Descriptor :=
  ArbitraryWidthHighLayout.originalDescriptor (v.beforeRows*v.rows*v.beforeH)
    v.width v.between v.afterD

theorem folded_volume (q : ℕ) (v : Descriptor) : volume q v = volume q (folded v) :=
  ArbitraryWidthHighPrefix.folded_volume q _ _ _ _ _ _

theorem folded_positive (v : Descriptor) (hv : v.Positive) : (folded v).Positive :=
  ⟨Nat.mul_pos (Nat.mul_pos hv.1 hv.2.1) hv.2.2.1,by change 0 < 1; decide,by change 0 < 1; decide,
    hv.2.2.2.1,hv.2.2.2.2⟩

def foldAddress {v : Descriptor} (x : Address v) : Address (folded v) where
  beforeRows := finProdFinEquiv (finProdFinEquiv (x.beforeRows,x.row),x.before)
  row := ⟨0,by change 0 < 1; decide⟩
  before := ⟨0,by change 0 < 1; decide⟩
  h := x.h
  middle := x.middle
  d := x.d
  after := x.after

theorem foldAddress_index {v : Descriptor} (x : Address v) :
    RecursiveInterchangeScaling.index (foldAddress x) =
      Fin.cast (folded_volume prime v) (RecursiveInterchangeScaling.index x) := by
  apply Fin.ext
  simp only [Fin.val_cast,RecursiveInterchangeScaling.index_val]
  change RecursiveInterchangeLayout.index prime (folded v)
    (finProdFinEquiv (finProdFinEquiv (x.beforeRows,x.row),x.before)).val 0 0
    x.h.val x.middle.val x.d.val x.after.val = _
  have hp : (finProdFinEquiv (finProdFinEquiv (x.beforeRows,x.row),x.before)).val =
      (x.beforeRows.val*v.rows+x.row.val)*v.beforeH+x.before.val := by
    simp [finProdFinEquiv]
    ring
  rw [hp]
  exact (ArbitraryWidthHighPrefix.folded_index prime v.beforeRows v.rows v.beforeH
    v.width v.between v.afterD x.beforeRows.val x.row.val x.before.val
    x.h.val x.middle.val x.d.val x.after.val).symm

theorem foldAddress_swap {v : Descriptor} (x : Address v) :
    foldAddress (Shared50RecursiveNodeTranspose.swapAddress x) =
      Shared50RecursiveNodeTranspose.swapAddress (foldAddress x) := rfl

theorem index_surjective (v : Descriptor) : Function.Surjective
    (RecursiveInterchangeScaling.index (v := v)) := by
  intro z
  let p6 := finProdFinEquiv.symm z
  let p5 := finProdFinEquiv.symm p6.1
  let p4 := finProdFinEquiv.symm p5.1
  let p3 := finProdFinEquiv.symm p4.1
  let p2 := finProdFinEquiv.symm p3.1
  let p1 := finProdFinEquiv.symm p2.1
  refine ⟨⟨p1.1,p1.2,p2.2,p3.2,p4.2,p5.2,p6.2⟩,?_⟩
  change finProdFinEquiv (finProdFinEquiv (finProdFinEquiv
    (finProdFinEquiv (finProdFinEquiv (finProdFinEquiv (p1.1,p1.2),p2.2),p3.2),p4.2),p5.2),p6.2) = z
  simp only [p1,p2,p3,p4,p5,p6,Prod.eta,Equiv.apply_symm_apply]
  exact finProdFinEquiv.apply_symm_apply z

/-- No data movement: the two arrays use precisely the same serialized cell. -/
def foldArray {α : Type*} {v : Descriptor} (x : Fin (volume prime v) → α) :
    Fin (volume prime (folded v)) → α :=
  fun z => x (Fin.cast (folded_volume prime v).symm z)

@[simp] theorem foldArray_entry {α : Type*} {v : Descriptor}
    (x : Fin (volume prime v) → α) (z : Fin (volume prime v)) :
    foldArray x (Fin.cast (folded_volume prime v) z) = x z := by
  simp [foldArray]

/-- Complete H/D interchange is independent of the original row/prefix
factorization and of the cyclic role divisor chosen for that descriptor. -/
theorem transpose_fold {α : Type*} {v : Descriptor} {c : ℕ}
    (hc : 0 < c) (hd : c ∣ v.rows) (x : Fin (volume prime v) → α) :
    Shared50RecursiveNodeRows.transpose (one_dvd _) (foldArray x) =
      foldArray (Shared50RecursiveNodeRows.transpose hd x) := by
  funext z
  obtain ⟨a,ha⟩ := index_surjective v (Fin.cast (folded_volume prime v).symm z)
  have hz : Fin.cast (folded_volume prime v) (RecursiveInterchangeScaling.index a) = z := by
    rw [ha]
    simp
  rw [← hz,← foldAddress_index]
  have hf := Shared50RecursiveNodeTranspose.transpose_all (by decide : 0 < 1)
    (one_dvd _) (foldArray x) (Shared50RecursiveNodeTranspose.swapAddress (foldAddress a))
  have ho := Shared50RecursiveNodeTranspose.transpose_all hc hd x
    (Shared50RecursiveNodeTranspose.swapAddress a)
  have hs : Shared50RecursiveNodeTranspose.swapAddress
      (Shared50RecursiveNodeTranspose.swapAddress a) = a := rfl
  have hsf : Shared50RecursiveNodeTranspose.swapAddress
      (Shared50RecursiveNodeTranspose.swapAddress (foldAddress a)) = foldAddress a := rfl
  rw [hs] at ho
  rw [hsf,← foldAddress_swap] at hf
  simp only [foldAddress_index,foldArray_entry] at hf ⊢
  rw [hf,ho]

/-- The cast preserves the actual serialized input list, including its order. -/
theorem foldArray_word {α : Type*} {v : Descriptor} (x : Fin (volume prime v) → α) :
    List.ofFn (foldArray x) = List.ofFn x :=
  (List.ofFn_congr (folded_volume prime v) x).symm

theorem foldArray_encoded {v : Descriptor} (x : Fin (volume prime v) → ZMod 2) :
    Shared50RecursiveNodeSemantics.encoded (foldArray x) =
      foldArray (Shared50RecursiveNodeSemantics.encoded x) := rfl

theorem foldArray_encoded_word {v : Descriptor} (x : Fin (volume prime v) → ZMod 2) :
    List.ofFn (Shared50RecursiveNodeSemantics.encoded (foldArray x)) =
      List.ofFn (Shared50RecursiveNodeSemantics.encoded x) := by
  rw [foldArray_encoded,foldArray_word]

theorem encoded_transpose_fold {v : Descriptor} {c : ℕ} (hc : 0 < c) (hd : c ∣ v.rows)
    (x : Fin (volume prime v) → ZMod 2) :
    Shared50RecursiveNodeRows.transpose (one_dvd _)
      (Shared50RecursiveNodeSemantics.encoded (foldArray x)) =
      foldArray (Shared50RecursiveNodeRows.transpose hd
        (Shared50RecursiveNodeSemantics.encoded x)) := by
  rw [foldArray_encoded,transpose_fold hc hd]

end
end IntegerMultBounds.Machine.ArbitraryWidthHighFoldSemantics
