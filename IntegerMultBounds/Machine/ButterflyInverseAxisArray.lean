import IntegerMultBounds.Machine.ButterflyInverseAxisOriginal
import IntegerMultBounds.Machine.ButterflyAxisWalsh

/-! Exact common-array endpoints and dyadic guard for the native inverse axis.
The inverse merge changes physical stream order; no free array permutation is
assumed at the clean endpoint. -/
namespace IntegerMultBounds.Machine.ButterflyInverseAxisArray
noncomputable section
open ButterflyAxisArray ButterflyAxisSemantics ButterflyAxisDecoded
open ButterflyStreamData ButterflyStreamSemantics
open ButterflyAxisHeadersData ButterflyAxisHeadersGeometry

def applyAxis (D t R p : ℕ) (ht : t<D) (f : Array D R) : Array D R :=
  unshape D t R p ht (ButterflyInverseAxisRouting.transformed (reshape D t R p ht f))

theorem width_apply (D t R p : ℕ) (ht : t<D) (f : Array D R) (hw : Width D R p f) :
    Width D R p (applyAxis D t R p ht f) := by
  intro i
  unfold applyAxis unshape ButterflyAxisSerialization.joined
  exact ButterflyInverseAxisRouting.transformed_width (reshape D t R p ht f) (ButterflyGuard.width p D)
    (fun h j k => hw _) _ _ _

theorem runs (D t R p : ℕ) (ht : t<D) (hR : 0<R) (f : Array D R) (hw : Width D R p f) :
    HoareTime ButterflyInverseAxisOriginal.program
      (fun z => z=ButterflyAxisOriginal.bank D t R p (full (fun _ => blank) 0 f))
      (fun z => z=ButterflyAxisOriginal.bank D (t+1) R p (full (fun _ => blank) 0 (applyAxis D t R p ht f)))
      (ButterflyAxisOriginal.constant*ButterflyAxisHeadersBudget.logicalVolume D R p) := by
  have hh := ButterflyInverseAxisOriginal.runs D t R p ht hR (reshape D t R p ht f) (fun h j k => hw _)
  rw [source_word,word_unshape D t R p ht] at hh
  exact hh

theorem grid_apply (D t R p j : ℕ) (ht : t<D) (hj : j≤D)
    (f : Array D R) (hw : Width D R p f) (hg : Grid D R p j f) :
    Grid D R p (j+1) (applyAxis D t R p ht f) := by
  intro i
  unfold applyAxis unshape ButterflyAxisSerialization.joined ButterflyInverseAxisRouting.transformed
    ButterflyInverseAxisRouting.swapped ButterflyStreamSemantics.transformed
  exact result_grid _ _ p D j hj (hw _) (hw _) (hg _) (hg _) _

/-- The inverse swaps the two forward butterfly outputs in each actual pair. -/
def axis (D t R p : ℕ) (ht : t<D) (f : Fin (Size D R) → ℂ) :=
  ButterflyAxisKernel.translation D t R p ht (ButterflyAxisDecoded.axis D t R p ht f)

theorem decoded_apply (D t R p j : ℕ) (ht : t<D) (hj : j≤D)
    (f : Array D R) (hw : Width D R p f) (hg : Grid D R p j f) :
    decoded D R p (j+1) (applyAxis D t R p ht f)=axis D t R p ht (decoded D R p j f) := by
  unfold axis ButterflyAxisKernel.translation ButterflyAxisDecoded.axis
  simp only [ButterflyAxisKernel.view_join]
  funext i
  unfold decoded applyAxis unshape ButterflyAxisSerialization.joined ButterflyInverseAxisRouting.transformed
    ButterflyInverseAxisRouting.swapped ButterflyStreamSemantics.transformed join view reshape
  exact result_decode _ _ p D j hj (hw _) (hw _) (hg _) (hg _) _

end
end IntegerMultBounds.Machine.ButterflyInverseAxisArray
