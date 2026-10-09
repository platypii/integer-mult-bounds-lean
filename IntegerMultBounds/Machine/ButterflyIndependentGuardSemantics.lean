import IntegerMultBounds.Machine.ButterflyIndependentGuardHeaders

/-! The physically derived reservation q+2D gives signed width q+4D+4, while
actual arithmetic starts at precision q. Its semantic guard budget is 2D, so a
full forward pass and a full inverse pass share one unchanged record width. -/
namespace IntegerMultBounds.Machine.ButterflyIndependentGuardSemantics
noncomputable section
open ButterflyAxisArray (Array Size)
open ButterflyIndependentGuardHeaders (reservation)
open ButterflyStreamSemantics (decode)
open Networks.GaussianPrecision

abbrev Width (D R q : ℕ) (f : Array D R) := ButterflyAxisArray.Width D R (reservation D q) f

def decoded (D R q j : ℕ) (f : Array D R) : Fin (Size D R) → ℂ :=
  fun i => decode (ButterflyGuard.halfWidth q (2*D)) (q+j) (f i)

def Grid (D R q j : ℕ) (f : Array D R) :=
  ∀ i,BoundedGrid (q+j) (2^q*4^j) (decoded D R q j f i)

theorem half_eq (D q : ℕ) : ButterflyGuard.halfWidth (reservation D q) D=ButterflyGuard.halfWidth q (2*D) := by
  unfold ButterflyGuard.halfWidth reservation
  omega

theorem width_eq (D q : ℕ) : ButterflyGuard.width (reservation D q) D=ButterflyGuard.width q (2*D) := by
  simp only [ButterflyGuard.width,half_eq]

theorem initial_grid (D R q : ℕ) (f : Array D R) (hu : ∀ i,‖decoded D R q 0 f i‖≤1) : Grid D R q 0 f := by
  intro i
  have hh := ButterflyGuard.normalized_bound
    (ButterflySigned.signedValue (ButterflyGuard.halfWidth q (2*D)) (f i).1)
    (ButterflySigned.signedValue (ButterflyGuard.halfWidth q (2*D)) (f i).2) q (hu i)
  simp only [decoded,Nat.add_zero,pow_zero,mul_one]
  refine ⟨_,_,?_,hh.1,hh.2⟩
  unfold decode ButterflySigned.complexValue
  exact div_mul_cancel₀ _ (pow_ne_zero _ (by norm_num))

theorem forward_grid (D t R q j : ℕ) (ht : t<D) (hj : j≤2*D)
    (f : Array D R) (hw : Width D R q f) (hg : Grid D R q j f) :
    Grid D R q (j+1) (ButterflyAxisArray.applyAxis D t R (reservation D q) ht f) := by
  intro i
  unfold decoded ButterflyAxisArray.applyAxis ButterflyAxisArray.unshape ButterflyAxisSerialization.joined
    ButterflyStreamSemantics.transformed ButterflyAxisArray.reshape
  apply ButterflyStreamSemantics.result_grid _ _ q (2*D) j hj
  · simpa only [width_eq] using hw _
  · simpa only [width_eq] using hw _
  · exact hg _
  · exact hg _

theorem inverse_grid (D t R q j : ℕ) (ht : t<D) (hj : j≤2*D)
    (f : Array D R) (hw : Width D R q f) (hg : Grid D R q j f) :
    Grid D R q (j+1) (ButterflyInverseAxisArray.applyAxis D t R (reservation D q) ht f) := by
  intro i
  unfold decoded ButterflyInverseAxisArray.applyAxis ButterflyAxisArray.unshape ButterflyAxisSerialization.joined
    ButterflyInverseAxisRouting.transformed ButterflyInverseAxisRouting.swapped ButterflyStreamSemantics.transformed ButterflyAxisArray.reshape
  apply ButterflyStreamSemantics.result_grid _ _ q (2*D) j hj
  · simpa only [width_eq] using hw _
  · simpa only [width_eq] using hw _
  · exact hg _
  · exact hg _

theorem forward_decoded (D t R q j : ℕ) (ht : t<D) (hj : j≤2*D)
    (f : Array D R) (hw : Width D R q f) (hg : Grid D R q j f) :
    decoded D R q (j+1) (ButterflyAxisArray.applyAxis D t R (reservation D q) ht f)=
      ButterflyAxisDecoded.axis D t R (reservation D q) ht (decoded D R q j f) := by
  funext i
  unfold decoded ButterflyAxisArray.applyAxis ButterflyAxisArray.unshape ButterflyAxisSerialization.joined
    ButterflyStreamSemantics.transformed ButterflyAxisDecoded.axis ButterflyAxisDecoded.join
    ButterflyAxisDecoded.view ButterflyAxisArray.reshape
  apply ButterflyAxisDecoded.result_decode _ _ q (2*D) j hj
  · simpa only [width_eq] using hw _
  · simpa only [width_eq] using hw _
  · exact hg _
  · exact hg _

theorem inverse_decoded (D t R q j : ℕ) (ht : t<D) (hj : j≤2*D)
    (f : Array D R) (hw : Width D R q f) (hg : Grid D R q j f) :
    decoded D R q (j+1) (ButterflyInverseAxisArray.applyAxis D t R (reservation D q) ht f)=
      ButterflyInverseAxisArray.axis D t R (reservation D q) ht (decoded D R q j f) := by
  unfold ButterflyInverseAxisArray.axis ButterflyAxisKernel.translation ButterflyAxisDecoded.axis
  simp only [ButterflyAxisKernel.view_join]
  funext i
  unfold decoded ButterflyInverseAxisArray.applyAxis ButterflyAxisArray.unshape ButterflyAxisSerialization.joined
    ButterflyInverseAxisRouting.transformed ButterflyInverseAxisRouting.swapped ButterflyStreamSemantics.transformed
    ButterflyAxisDecoded.join ButterflyAxisDecoded.view ButterflyAxisArray.reshape
  apply ButterflyAxisDecoded.result_decode _ _ q (2*D) j hj
  · simpa only [width_eq] using hw _
  · simpa only [width_eq] using hw _
  · exact hg _
  · exact hg _

end
end IntegerMultBounds.Machine.ButterflyIndependentGuardSemantics
