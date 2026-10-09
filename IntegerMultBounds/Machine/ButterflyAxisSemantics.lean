import IntegerMultBounds.Machine.ButterflyAxisSchedule

/-! The actual global coefficient arrays retain a bounded Gaussian grid through
all counted axes. The precision increases once per pass; one fixed signed word
width suffices for the whole schedule, including every intermediate state. -/
namespace IntegerMultBounds.Machine.ButterflyAxisSemantics
noncomputable section
open ButterflyAxisArray ButterflyAxisSchedule ButterflyStreamSemantics
open ButterflyAxisSerialization
open Networks.GaussianPrecision

/-- The stage counts processed axes, independently of the selected axis number. -/
def Grid (D R p j : ℕ) (f : Array D R) : Prop :=
  ∀ i, BoundedGrid (p+j) (2^p*4^j)
    (decode (ButterflyGuard.halfWidth p D) (p+j) (f i))

theorem grid_apply (D t R p j : ℕ) (ht : t<D) (hj : j≤D)
    (f : Array D R) (hw : Width D R p f) (hg : Grid D R p j f) :
    Grid D R p (j+1) (applyAxis D t R p ht f) := by
  intro i
  unfold applyAxis unshape joined transformed
  exact result_grid _ _ p D j hj (hw _) (hw _) (hg _) (hg _) _

theorem grid_step (D t R p j : ℕ) (ht : t<D) (hj : j≤D)
    (f : Array D R) (hw : Width D R p f) (hg : Grid D R p j f) :
    Grid D R p (j+1) (ButterflyAxisSchedule.step D t R p f) := by
  rw [ButterflyAxisSchedule.step,dite_eq_left ht]
  exact grid_apply D t R p j ht hj f hw hg

theorem grid_run (D start R p n : ℕ) (hfit : start+n≤D)
    (f : Array D R) (hw : Width D R p f) (hg : Grid D R p 0 f) :
    Grid D R p n (ButterflyAxisSchedule.run D start R p n f) := by
  induction n with
  | zero => exact hg
  | succ n ih =>
    exact grid_step D (start+n) R p n (by omega) (by omega) _
      (width_run D start R p n f hw) (ih (by omega))

/-- The normalized input contract supplies the initial grid from the stored
integer numerators themselves; no independent codec witness is assumed. -/
theorem grid_initial (D R p : ℕ) (f : Array D R)
    (hn : ∀ i, ‖decode (ButterflyGuard.halfWidth p D) p (f i)‖≤1) :
    Grid D R p 0 f := by
  intro i
  have hh := ButterflyGuard.normalized_bound
    (ButterflySigned.signedValue (ButterflyGuard.halfWidth p D) (f i).1)
    (ButterflySigned.signedValue (ButterflyGuard.halfWidth p D) (f i).2) p (hn i)
  simp only [Nat.add_zero,pow_zero,mul_one]
  refine ⟨_,_,?_,hh.1,hh.2⟩
  unfold decode ButterflySigned.complexValue
  exact div_mul_cancel₀ _ (pow_ne_zero _ (by norm_num))

/-- Every actual prefix is representable at its exact dyadic precision and
stays strictly inside the signed arithmetic guard. -/
theorem prefixes (D start R p n : ℕ) (hfit : start+n≤D)
    (f : Array D R) (hw : Width D R p f)
    (hn : ∀ i, ‖decode (ButterflyGuard.halfWidth p D) p (f i)‖≤1)
    (j : ℕ) (hj : j≤n) :
    Width D R p (ButterflyAxisSchedule.run D start R p j f) ∧
    Grid D R p j (ButterflyAxisSchedule.run D start R p j f) ∧
    p+j≤p+D ∧ 4*(2^p*4^j)<2^(ButterflyGuard.halfWidth p D) := by
  exact ⟨width_run D start R p j f hw,
    grid_run D start R p j (by omega) f hw (grid_initial D R p f hn),
    ButterflyGuard.precision_le p D j (by omega),ButterflyGuard.guard p D j (by omega)⟩

end
end IntegerMultBounds.Machine.ButterflyAxisSemantics
