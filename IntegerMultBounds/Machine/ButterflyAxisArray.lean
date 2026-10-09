import IntegerMultBounds.Machine.ButterflyAxisOriginal

/-! A single global coefficient array has the same physical word for every
selected-axis view. Reshaping is a proved indexing identity, not a free tape
reorder; the actual machine performs the split and merge. -/
namespace IntegerMultBounds.Machine.ButterflyAxisArray
noncomputable section
open ButterflyStreamData ButterflyAxisSerialization
open ButterflyAxisHeadersData ButterflyAxisHeadersGeometry
open RecursiveInterchangeRows (pack)

abbrev Size (D R : ℕ) := 2^D*R
abbrev Array (D R : ℕ) := Fin (Size D R) → Coefficient

theorem size_eq (D t R p : ℕ) (ht : t<D) :
    RecursiveInterchangeRows.groups 2 (descriptor D t R p)*(2*lower t R)=Size D R := by
  rw [groups_eq]
  have he : (D-t-1)+t+1=D := by omega
  unfold higher lower Size
  calc
    _ = 2^((D-t-1)+t+1)*R := by rw [pow_add,pow_add,pow_one]; ring
    _ = _ := by rw [he]

def reshape (D t R p : ℕ) (ht : t<D) (f : Array D R)
    (h : Fin (RecursiveInterchangeRows.groups 2 (descriptor D t R p))) (j : Fin 2) (k : Fin (lower t R)) : Coefficient :=
  f (Fin.cast (size_eq D t R p ht) (pack h (pack j k)))

def unshape (D t R p : ℕ) (ht : t<D)
    (xs : Fin (RecursiveInterchangeRows.groups 2 (descriptor D t R p)) → Fin 2 → Fin (lower t R) → Coefficient)
    (i : Fin (Size D R)) : Coefficient := joined xs (Fin.cast (size_eq D t R p ht).symm i)

theorem joined_reshape (D t R p : ℕ) (ht : t<D) (f : Array D R)
    (i : Fin (RecursiveInterchangeRows.groups 2 (descriptor D t R p)*(2*lower t R))) :
    joined (reshape D t R p ht f) i=f (Fin.cast (size_eq D t R p ht) i) := by
  have hi : pack (finProdFinEquiv.symm i).1
      (pack (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).1
        (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).2)=i := by
    have hk : pack (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).1
        (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).2=(finProdFinEquiv.symm i).2 :=
      finProdFinEquiv.apply_symm_apply _
    rw [hk]
    exact finProdFinEquiv.apply_symm_apply i
  exact congrArg (fun k => f (Fin.cast (size_eq D t R p ht) k)) hi

theorem unshape_reshape (D t R p : ℕ) (ht : t<D) (f : Array D R) :
    unshape D t R p ht (reshape D t R p ht f)=f := by
  funext i
  rw [unshape,joined_reshape]
  simp

theorem word_unshape (D t R p : ℕ) (ht : t<D)
    (xs : Fin (RecursiveInterchangeRows.groups 2 (descriptor D t R p)) → Fin 2 → Fin (lower t R) → Coefficient) :
    ButterflyAxisBank.word xs=full (fun _ => blank) 0 (unshape D t R p ht xs) := by
  unfold ButterflyAxisBank.word full unshape
  rw [List.ofFn_congr (size_eq D t R p ht) (fun i => encoded (joined xs i))]

theorem source_word (D t R p : ℕ) (ht : t<D) (f : Array D R) :
    ButterflyAxisBank.word (reshape D t R p ht f)=full (fun _ => blank) 0 f := by
  rw [word_unshape D t R p ht,unshape_reshape]

def applyAxis (D t R p : ℕ) (ht : t<D) (f : Array D R) : Array D R :=
  unshape D t R p ht (ButterflyStreamSemantics.transformed (reshape D t R p ht f))

def Width (D R p : ℕ) (f : Array D R) : Prop :=
  ∀ i,(f i).1.length=ButterflyGuard.width p D ∧ (f i).2.length=ButterflyGuard.width p D

theorem width_apply (D t R p : ℕ) (ht : t<D) (f : Array D R) (hw : Width D R p f) :
    Width D R p (applyAxis D t R p ht f) := by
  intro i
  unfold applyAxis unshape joined
  exact ButterflyStreamSemantics.transformed_width (reshape D t R p ht f) (ButterflyGuard.width p D)
    (fun h j k => hw _) _ _ _

theorem runs (D t R p : ℕ) (ht : t<D) (hR : 0<R) (f : Array D R) (hw : Width D R p f) :
    HoareTime ButterflyAxisOriginal.program
      (fun z => z=ButterflyAxisOriginal.bank D t R p (full (fun _ => blank) 0 f))
      (fun z => z=ButterflyAxisOriginal.bank D (t+1) R p (full (fun _ => blank) 0 (applyAxis D t R p ht f)))
      (ButterflyAxisOriginal.constant*ButterflyAxisHeadersBudget.logicalVolume D R p) := by
  have hh := ButterflyAxisOriginal.runs D t R p ht hR (reshape D t R p ht f) (fun h j k => hw _)
  rw [source_word,word_unshape D t R p ht] at hh
  exact hh

end
end IntegerMultBounds.Machine.ButterflyAxisArray
