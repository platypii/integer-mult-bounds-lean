import IntegerMultBounds.Machine.ButterflyAxisDecoded

/-! The decoded selected-axis butterfly is exactly a translation kernel:
its translation exchanges the selected bit and preserves all other coordinates.
This identifies the arithmetic operator independently of its tape realization. -/
namespace IntegerMultBounds.Machine.ButterflyAxisKernel
noncomputable section
open ButterflyAxisArray ButterflyAxisDecoded
open ButterflyAxisHeadersGeometry ButterflyAxisHeadersData
open RecursiveInterchangeRows (pack)

def swapBit : Equiv.Perm (Fin 2) := Equiv.swap 0 1

theorem butterfly_linear (f : Fin 2 → ℂ) (k : Fin 2) :
    butterfly k (f 0) (f 1)=((1+Complex.I)/2)*f k+((1-Complex.I)/2)*f (swapBit k) := by
  fin_cases k <;> simp [butterfly,swapBit] <;> ring

theorem join_view {α : Type*} (D t R p : ℕ) (ht : t<D) (f : Fin (Size D R) → α) :
    join D t R p ht (view D t R p ht f)=f := by
  funext i
  unfold join view
  dsimp only
  have hk : pack
      (finProdFinEquiv.symm (finProdFinEquiv.symm (Fin.cast (size_eq D t R p ht).symm i)).2).1
      (finProdFinEquiv.symm (finProdFinEquiv.symm (Fin.cast (size_eq D t R p ht).symm i)).2).2 =
      (finProdFinEquiv.symm (Fin.cast (size_eq D t R p ht).symm i)).2 :=
    finProdFinEquiv.apply_symm_apply _
  rw [hk]
  change f (Fin.cast (size_eq D t R p ht)
    (finProdFinEquiv (finProdFinEquiv.symm (Fin.cast (size_eq D t R p ht).symm i))))=f i
  rw [finProdFinEquiv.apply_symm_apply]
  rfl

theorem view_join {α : Type*} (D t R p : ℕ) (ht : t<D)
    (xs : Fin (RecursiveInterchangeRows.groups 2 (descriptor D t R p)) → Fin 2 → Fin (lower t R) → α)
    (h : Fin (RecursiveInterchangeRows.groups 2 (descriptor D t R p))) (j : Fin 2) (k : Fin (lower t R)) :
    view D t R p ht (join D t R p ht xs) h j k=xs h j k := by
  simp only [view,join,Fin.cast_cast,Fin.cast_eq_self,pack,Equiv.symm_apply_apply]

/-- Flip the selected bit while leaving higher and lower coordinates fixed. -/
def translation {α : Type*} (D t R p : ℕ) (ht : t<D) (f : Fin (Size D R) → α) : Fin (Size D R) → α :=
  join D t R p ht (fun h k l => view D t R p ht f h (swapBit k) l)

theorem axis_kernel (D t R p : ℕ) (ht : t<D) (f : Fin (Size D R) → ℂ) (i : Fin (Size D R)) :
    axis D t R p ht f i=((1+Complex.I)/2)*f i+((1-Complex.I)/2)*translation D t R p ht f i := by
  have hh := congrFun (join_view D t R p ht f) i
  rw [←hh]
  unfold axis translation join
  dsimp only
  exact butterfly_linear (fun k => view D t R p ht f
    (finProdFinEquiv.symm (Fin.cast (size_eq D t R p ht).symm i)).1 k
    (finProdFinEquiv.symm (finProdFinEquiv.symm (Fin.cast (size_eq D t R p ht).symm i)).2).2) _

/-- The selected coordinate exchange really is an involutive translation. -/
theorem translation_involutive {α : Type*} (D t R p : ℕ) (ht : t<D) (f : Fin (Size D R) → α) :
    translation D t R p ht (translation D t R p ht f)=f := by
  unfold translation
  have hh : (fun h k l => view D t R p ht
      (join D t R p ht (fun h k l => view D t R p ht f h (swapBit k) l)) h (swapBit k) l)=
      view D t R p ht f := by
    funext h k l
    rw [view_join]
    simp only [swapBit,Equiv.swap_apply_self]
  rw [hh,join_view]

end
end IntegerMultBounds.Machine.ButterflyAxisKernel
