import IntegerMultBounds.Machine.CompactComplexChildGridAlignment

/-! Shared-grid promotion after a stopped child fits the actual sibling
return ledger. The denominator increases by the child axis count; the
numerator budget reserves two butterfly contributions per returned sibling
axis, independently of that denominator. -/
namespace IntegerMultBounds.Machine.CompactComplexChildGridReturnBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid CompactComplexChildGridAlignment
open Networks.GaussianPrecision

theorem returned_bound (p C levels frames returned gap : ℕ) :
    CompactRecursiveGridBudget.bound p C levels (frames+2*returned)*4^gap ≤
      CompactRecursiveGridBudget.bound p C levels (frames+2*(returned+gap)) := by
  have he : frames+2*(returned+gap)=frames+2*returned+2*gap := by omega
  rw [he]
  unfold CompactRecursiveGridBudget.bound
  simp only [pow_add,←Nat.mul_assoc]
  exact Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right (by decide : 0<4) (by omega : gap≤2*gap))

/-- A genuine completed selected child plus exact spectator promotion
discharges the common-grid sibling endpoint at the reserved returned budget. -/
theorem shared_grid_returned {ι : Type*} [DecidableEq ι]
    (s : Shape) (rows ell q n p C levels frames returned gap : ℕ) (selected : ι)
    (before after : ι → Array s rows ell)
    (hbefore : ∀ role,Grid s rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) (before role))
    (hchild : Grid s rows ell q (n+gap)
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)*4^gap) (after selected))
    (hpromote : ∀ role,role≠selected → ∀ i,
      Promotes (half s q) gap (before role i) (after role i)) :
    (∀ role,Grid s rows ell q (n+gap)
      (CompactRecursiveGridBudget.bound p C levels (frames+2*(returned+gap))) (after role)) ∧
      (∀ role,role≠selected → decoded s rows ell q (n+gap) (after role) =
        decoded s rows ell q n (before role)) := by
  obtain ⟨hgrid,hvalues⟩ := shared_grid s rows ell q n _ gap selected before after hbefore hchild hpromote
  refine ⟨?_,hvalues⟩
  intro role i
  exact bound_mono (returned_bound p C levels frames returned gap) (hgrid role i)

end
end IntegerMultBounds.Machine.CompactComplexChildGridReturnBudget
