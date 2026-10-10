import IntegerMultBounds.Machine.CompactSpectatorInheritedGrid
import IntegerMultBounds.Machine.SignedRadixExactReturn

/-! The shared dyadic grid after a selected-role child is established by
actual numerator promotion of every spectator. Equal record widths alone
do not establish this handoff. The physical promotion machine supplies the
signed-numerator equations consumed here. -/
namespace IntegerMultBounds.Machine.CompactComplexChildGridAlignment
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid
open Networks.GaussianPrecision

/-- Exact semantic contract required of the physical fixed-width promotion. -/
def Promotes (b gap : ℕ) (before after : ButterflyStreamData.Coefficient) : Prop :=
  ButterflySigned.signedValue b after.1 = ButterflySigned.signedValue b before.1 * 2^gap ∧
  ButterflySigned.signedValue b after.2 = ButterflySigned.signedValue b before.2 * 2^gap

theorem decode_promotes (b n gap : ℕ)
    (before after : ButterflyStreamData.Coefficient) (h : Promotes b gap before after) :
    ButterflyStreamSemantics.decode b (n+gap) after =
      ButterflyStreamSemantics.decode b n before := by
  unfold ButterflyStreamSemantics.decode
  rw [h.1,h.2]
  exact SignedRadixExactReturn.complex_raise _ _ n gap

/-- The returned selected stream and physically promoted spectators now
have one common denominator, with the same conservative child growth bound. -/
theorem shared_grid {ι : Type*} [DecidableEq ι]
    (s : Shape) (rows ell q n M gap : ℕ) (selected : ι)
    (before after : ι → Array s rows ell)
    (hbefore : ∀ role,Grid s rows ell q n M (before role))
    (hchild : Grid s rows ell q (n+gap) (M*4^gap) (after selected))
    (hpromote : ∀ role,role≠selected → ∀ i,
      Promotes (half s q) gap (before role i) (after role i)) :
    (∀ role,Grid s rows ell q (n+gap) (M*4^gap) (after role)) ∧
      (∀ role,role≠selected → decoded s rows ell q (n+gap) (after role) =
        decoded s rows ell q n (before role)) := by
  have hp : 2^gap≤4^gap := Nat.pow_le_pow_left (by decide) gap
  have hs : ∀ role,role≠selected → decoded s rows ell q (n+gap) (after role) =
      decoded s rows ell q n (before role) := by
    intro role hr
    funext i
    exact decode_promotes _ n gap _ _ (hpromote role hr i)
  refine ⟨?_,hs⟩
  intro role i
  by_cases hr : role=selected
  · subst role
    exact hchild i
  · rw [hs role hr]
    exact bound_mono (Nat.mul_le_mul_left M hp) (bounded_raise (hbefore role i) gap)

/-- Specialization to the exact directional stream computed by the stopped
child. The selected-role grid is derived from the child arithmetic rather
than supplied as an independent endpoint certificate. -/
theorem stopped_shared_grid {ι : Type*} [DecidableEq ι]
    (s : Shape) (rows ell q n M : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : CompactComplexRecursiveGeometry.Visit s.active left k)
    (dir : CompactSpectatorLeafGuardOriginal.Direction) (selected : ι)
    (before after : ι → Array s rows ell)
    (hwidth : Width s rows ell q (before selected))
    (hbefore : ∀ role,Grid s rows ell q n M (before role))
    (hguard : 4*(M*4^(CompactComplexRecursiveGeometry.arity^k))<2^(half s q))
    (hchild : after selected = CompactSpectatorLeafGuardOriginal.result
      dir s rows ell q rho visit (before selected))
    (hpromote : ∀ role,role≠selected → ∀ i,
      Promotes (half s q) (CompactComplexRecursiveGeometry.arity^k)
        (before role i) (after role i)) :
    (∀ role,Grid s rows ell q (n+CompactComplexRecursiveGeometry.arity^k)
      (M*4^(CompactComplexRecursiveGeometry.arity^k)) (after role)) ∧
      (∀ role,role≠selected →
        decoded s rows ell q (n+CompactComplexRecursiveGeometry.arity^k) (after role) =
        decoded s rows ell q n (before role)) := by
  apply shared_grid s rows ell q n M _ selected before after hbefore _ hpromote
  rw [hchild]
  cases dir
  · exact forward_grid s rows ell q rho visit _ n M le_rfl
      (before selected) hwidth (hbefore selected) hguard
  · exact inverse_grid s rows ell q rho visit _ n M le_rfl
      (before selected) hwidth (hbefore selected) hguard

/-- The actual dependency-path guard pays for spectator promotion as well
as for the selected child's butterfly work, without changing stored widths. -/
theorem promotion_capacity_from_path (s : Shape) (q : ℕ)
    {left k levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path s.active left k levels frames returned)
    (p C gap : ℕ) (hp : p≤q)
    (hchunk : dependencyCoefficient C≤s.chunk) (hgap : gap≤s.bits) :
    CompactRecursiveGridBudget.bound p C levels (frames+2*returned)*2^gap <
      2^(half s q) := by
  have hguard := guard_from_path s q path p C gap hp hchunk hgap
  have hpow : 2^gap≤4^gap := Nat.pow_le_pow_left (by decide) gap
  have hm := Nat.mul_le_mul_left (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) hpow
  omega

theorem promotion_guard_from_path (s : Shape) (q : ℕ)
    {left k levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path s.active left k levels frames returned)
    (p C n gap : ℕ) (hp : p≤q)
    (hchunk : dependencyCoefficient C≤s.chunk) (hgap : gap≤s.bits)
    (f : Array s rows ell)
    (hg : Grid s rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) f) (i : _) :
    |ButterflySigned.signedValue (half s q) (f i).1 * 2^gap| < (2^(half s q):ℕ) ∧
    |ButterflySigned.signedValue (half s q) (f i).2 * 2^gap| < (2^(half s q):ℕ) := by
  have hb := ButterflyGuard.represented_bound _ _ n _ (hg i)
  have hnat := promotion_capacity_from_path s q path p C gap hp hchunk hgap
  have hi : (CompactRecursiveGridBudget.bound p C levels (frames+2*returned):ℤ)*2^gap <
      (2^(half s q):ℕ) := by exact_mod_cast hnat
  have hnon : (0:ℤ)≤2^gap := by positivity
  constructor
  · rw [abs_mul,abs_of_nonneg hnon]
    exact (mul_le_mul_of_nonneg_right hb.1 hnon).trans_lt hi
  · rw [abs_mul,abs_of_nonneg hnon]
    exact (mul_le_mul_of_nonneg_right hb.2 hnon).trans_lt hi

/-- A genuine half-grid value cannot in general be returned to the parent's
integer grid. Consequently exact lowering needs an additional divisibility
proof; the child width and its finer-grid certificate cannot supply one. -/
theorem half_grid_not_parent (n M : ℕ) :
    ¬BoundedGrid n M (ButterflySigned.complexValue 1 1 (n+1)) := by
  intro h
  have hd := (SignedRadixExactReturn.coarser_divisibility 1 1 n 1 M h).1
  norm_num at hd

end
end IntegerMultBounds.Machine.CompactComplexChildGridAlignment
