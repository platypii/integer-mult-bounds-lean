import IntegerMultBounds.Machine.ButterflyInverseSpectatorGeometry
import IntegerMultBounds.Machine.ButterflyIndependentGuardSemantics

/-! Every full-address row-major spectator axis has exact complex semantics.
The baseline precision q advances once per executed axis; a single two-pass
reservation fixes all signed record widths. Prefix grids propagate without
renormalization, including from forward output into the inverse pass. -/
namespace IntegerMultBounds.Machine.ButterflySpectatorSemantics
noncomputable section
open ButterflySpectatorGeometry
open ButterflyStreamSemantics (decode)
open Networks.GaussianPrecision
open RecursiveInterchangeRows (pack)
open ButterflyIndependentGuardHeaders (reservation)

abbrev Width (rows D R q : ℕ) (f : Array rows D R) := ButterflySpectatorGeometry.Width rows D R (reservation D q) f

def decoded (rows D R q j : ℕ) (f : Array rows D R) : Fin (Size rows D R) → ℂ :=
  fun i => decode (ButterflyGuard.halfWidth q (2*D)) (q+j) (f i)
def Grid (rows D R q j : ℕ) (f : Array rows D R) :=
  ∀ i,BoundedGrid (q+j) (2^q*4^j) (decoded rows D R q j f i)

def view {α : Type*} (rows D t R p : ℕ) (ht : t<D) (f : Fin (Size rows D R) → α)
    (h : Fin (RecursiveInterchangeRows.groups 2 (descriptor rows D t R p)))
    (j : Fin 2) (k : Fin (ButterflyAxisHeadersData.lower t R)) : α :=
  f (Fin.cast (size_eq rows D t R p ht) (pack h (pack j k)))
def join {α : Type*} (rows D t R p : ℕ) (ht : t<D)
    (xs : Fin (RecursiveInterchangeRows.groups 2 (descriptor rows D t R p)) → Fin 2 →
      Fin (ButterflyAxisHeadersData.lower t R) → α) (i : Fin (Size rows D R)) : α :=
  let hjk := finProdFinEquiv.symm (Fin.cast (size_eq rows D t R p ht).symm i)
  let jk := finProdFinEquiv.symm hjk.2
  xs hjk.1 jk.1 jk.2

theorem join_view {α : Type*} (rows D t R p : ℕ) (ht : t<D) (f : Fin (Size rows D R) → α) :
    join rows D t R p ht (view rows D t R p ht f)=f := by
  funext i
  unfold join view
  dsimp only
  have hk : pack
      (finProdFinEquiv.symm (finProdFinEquiv.symm (Fin.cast (size_eq rows D t R p ht).symm i)).2).1
      (finProdFinEquiv.symm (finProdFinEquiv.symm (Fin.cast (size_eq rows D t R p ht).symm i)).2).2 =
      (finProdFinEquiv.symm (Fin.cast (size_eq rows D t R p ht).symm i)).2 :=
    finProdFinEquiv.apply_symm_apply _
  rw [hk]
  change f (Fin.cast (size_eq rows D t R p ht)
    (finProdFinEquiv (finProdFinEquiv.symm (Fin.cast (size_eq rows D t R p ht).symm i))))=f i
  rw [finProdFinEquiv.apply_symm_apply]
  rfl

theorem view_join {α : Type*} (rows D t R p : ℕ) (ht : t<D)
    (xs : Fin (RecursiveInterchangeRows.groups 2 (descriptor rows D t R p)) → Fin 2 →
      Fin (ButterflyAxisHeadersData.lower t R) → α)
    (h : Fin (RecursiveInterchangeRows.groups 2 (descriptor rows D t R p)))
    (j : Fin 2) (k : Fin (ButterflyAxisHeadersData.lower t R)) :
    view rows D t R p ht (join rows D t R p ht xs) h j k=xs h j k := by
  simp only [view,join,Fin.cast_cast,Fin.cast_eq_self,pack,Equiv.symm_apply_apply]

theorem view_row {α : Type*} (rows D t R p : ℕ) (ht : t<D) (f : Fin (Size rows D R) → α)
    (row : Fin rows) (h : Fin (ButterflyAxisHeadersData.higher D t))
    (j : Fin 2) (k : Fin (ButterflyAxisHeadersData.lower t R)) :
    view rows D t R p ht f (Fin.cast (groups_eq rows D t R p).symm (pack row h)) j k=
      ButterflyAxisDecoded.view D t R p ht (fun i => f (pack row i))
        (Fin.cast (ButterflyAxisHeadersGeometry.groups_eq D t R p).symm h) j k := by
  unfold view ButterflyAxisDecoded.view
  apply congrArg f
  apply Fin.ext
  simp only [Fin.val_cast,RecursiveInterchangeRows.pack_val]
  have he := ButterflyAxisArray.size_eq D t R p ht
  rw [ButterflyAxisHeadersGeometry.groups_eq] at he
  unfold ButterflyAxisArray.Size at he
  rw [←he]
  ring

theorem join_row {α : Type*} (rows D t R p : ℕ) (ht : t<D)
    (xs : Fin (RecursiveInterchangeRows.groups 2 (descriptor rows D t R p)) → Fin 2 →
      Fin (ButterflyAxisHeadersData.lower t R) → α) (row : Fin rows) :
    (fun i => join rows D t R p ht xs (pack row i))=
      ButterflyAxisDecoded.join D t R p ht (fun h j k =>
        xs (Fin.cast (groups_eq rows D t R p).symm
          (pack row (Fin.cast (ButterflyAxisHeadersGeometry.groups_eq D t R p) h))) j k) := by
  have hh : ButterflyAxisDecoded.view D t R p ht (fun i => join rows D t R p ht xs (pack row i))=
      (fun h j k => xs (Fin.cast (groups_eq rows D t R p).symm
          (pack row (Fin.cast (ButterflyAxisHeadersGeometry.groups_eq D t R p) h))) j k) := by
    funext h j k
    have hc := (view_row rows D t R p ht (join rows D t R p ht xs) row
      (Fin.cast (ButterflyAxisHeadersGeometry.groups_eq D t R p) h) j k).symm
    simpa only [Fin.cast_cast,Fin.cast_eq_self,view_join] using hc
  rw [← hh,ButterflyAxisKernel.join_view]

def axis (rows D t R p : ℕ) (ht : t<D) (f : Fin (Size rows D R) → ℂ) :=
  join rows D t R p ht (fun h j k => ButterflyAxisDecoded.butterfly j
    (view rows D t R p ht f h 0 k) (view rows D t R p ht f h 1 k))
def inverseAxis (rows D t R p : ℕ) (ht : t<D) (f : Fin (Size rows D R) → ℂ) :=
  join rows D t R p ht (fun h j k => ButterflyAxisDecoded.butterfly (ButterflyAxisKernel.swapBit j)
    (view rows D t R p ht f h 0 k) (view rows D t R p ht f h 1 k))

theorem axis_row (rows D t R p : ℕ) (ht : t<D) (f : Fin (Size rows D R) → ℂ) (row : Fin rows) :
    (fun i => axis rows D t R p ht f (pack row i))=
      ButterflyAxisDecoded.axis D t R p ht (fun i => f (pack row i)) := by
  unfold axis ButterflyAxisDecoded.axis
  rw [join_row]
  congr 1
  funext h j k
  rw [view_row,view_row]
  rfl

theorem inverse_row (rows D t R p : ℕ) (ht : t<D) (f : Fin (Size rows D R) → ℂ) (row : Fin rows) :
    (fun i => inverseAxis rows D t R p ht f (pack row i))=
      ButterflyInverseAxisArray.axis D t R p ht (fun i => f (pack row i)) := by
  unfold inverseAxis ButterflyInverseAxisArray.axis ButterflyAxisKernel.translation ButterflyAxisDecoded.axis
  simp only [ButterflyAxisKernel.view_join]
  rw [join_row]
  congr 1
  funext h j k
  rw [view_row,view_row]
  rfl

theorem initial_grid (rows D R q : ℕ) (f : Array rows D R)
    (hu : ∀ i,‖decoded rows D R q 0 f i‖≤1) : Grid rows D R q 0 f := by
  intro i
  have hh := ButterflyGuard.normalized_bound
    (ButterflySigned.signedValue (ButterflyGuard.halfWidth q (2*D)) (f i).1)
    (ButterflySigned.signedValue (ButterflyGuard.halfWidth q (2*D)) (f i).2) q (hu i)
  simp only [decoded,Nat.add_zero,pow_zero,mul_one]
  refine ⟨_,_,?_,hh.1,hh.2⟩
  unfold decode ButterflySigned.complexValue
  exact div_mul_cancel₀ _ (pow_ne_zero _ (by norm_num))

theorem forward_grid (rows D t R q j : ℕ) (ht : t<D) (hj : j≤2*D)
    (f : Array rows D R) (hw : Width rows D R q f) (hg : Grid rows D R q j f) :
    Grid rows D R q (j+1) (applyAxis rows D t R (reservation D q) ht f) := by
  intro i
  unfold decoded applyAxis unshape ButterflyAxisSerialization.joined ButterflyStreamSemantics.transformed reshape
  apply ButterflyStreamSemantics.result_grid _ _ q (2*D) j hj
  · simpa only [ButterflyIndependentGuardSemantics.width_eq] using hw _
  · simpa only [ButterflyIndependentGuardSemantics.width_eq] using hw _
  · exact hg _
  · exact hg _

theorem inverse_grid (rows D t R q j : ℕ) (ht : t<D) (hj : j≤2*D)
    (f : Array rows D R) (hw : Width rows D R q f) (hg : Grid rows D R q j f) :
    Grid rows D R q (j+1) (ButterflyInverseSpectatorGeometry.applyAxis rows D t R (reservation D q) ht f) := by
  intro i
  unfold decoded ButterflyInverseSpectatorGeometry.applyAxis unshape ButterflyAxisSerialization.joined
    ButterflyInverseAxisRouting.transformed ButterflyInverseAxisRouting.swapped ButterflyStreamSemantics.transformed reshape
  apply ButterflyStreamSemantics.result_grid _ _ q (2*D) j hj
  · simpa only [ButterflyIndependentGuardSemantics.width_eq] using hw _
  · simpa only [ButterflyIndependentGuardSemantics.width_eq] using hw _
  · exact hg _
  · exact hg _

theorem forward_decoded (rows D t R q j : ℕ) (ht : t<D) (hj : j≤2*D)
    (f : Array rows D R) (hw : Width rows D R q f) (hg : Grid rows D R q j f) :
    decoded rows D R q (j+1) (applyAxis rows D t R (reservation D q) ht f)=
      axis rows D t R (reservation D q) ht (decoded rows D R q j f) := by
  funext i
  unfold decoded applyAxis unshape ButterflyAxisSerialization.joined
    ButterflyStreamSemantics.transformed axis join view reshape
  apply ButterflyAxisDecoded.result_decode _ _ q (2*D) j hj
  · simpa only [ButterflyIndependentGuardSemantics.width_eq] using hw _
  · simpa only [ButterflyIndependentGuardSemantics.width_eq] using hw _
  · exact hg _
  · exact hg _

theorem inverse_decoded (rows D t R q j : ℕ) (ht : t<D) (hj : j≤2*D)
    (f : Array rows D R) (hw : Width rows D R q f) (hg : Grid rows D R q j f) :
    decoded rows D R q (j+1) (ButterflyInverseSpectatorGeometry.applyAxis rows D t R (reservation D q) ht f)=
      inverseAxis rows D t R (reservation D q) ht (decoded rows D R q j f) := by
  funext i
  unfold decoded ButterflyInverseSpectatorGeometry.applyAxis unshape ButterflyAxisSerialization.joined
    ButterflyInverseAxisRouting.transformed ButterflyInverseAxisRouting.swapped
    ButterflyStreamSemantics.transformed inverseAxis join view reshape
  apply ButterflyAxisDecoded.result_decode _ _ q (2*D) j hj
  · simpa only [ButterflyIndependentGuardSemantics.width_eq] using hw _
  · simpa only [ButterflyIndependentGuardSemantics.width_eq] using hw _
  · exact hg _
  · exact hg _

end
end IntegerMultBounds.Machine.ButterflySpectatorSemantics
