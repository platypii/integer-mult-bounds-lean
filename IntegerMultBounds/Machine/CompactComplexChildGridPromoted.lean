import IntegerMultBounds.Machine.CompactComplexChildGridAlignment
import IntegerMultBounds.Machine.NativeSignedGapPromoteWord
import IntegerMultBounds.Machine.CompactComplexChildGridReturnBudget

/-! Actual literal promoted spectator words give the shared grid required by
scalar streams after a stopped child. Their signed equations and capacity
follow from the original dependency Path, not a supplied promotion contract. -/
namespace IntegerMultBounds.Machine.CompactComplexChildGridPromoted
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid
open CompactComplexChildGridAlignment (Promotes)
open ButterflyStreamData (Coefficient)

def coefficient (gap : ℕ) (x : Coefficient) : Coefficient :=
  (NativeSignedGapPromoteWord.result gap x.1,NativeSignedGapPromoteWord.result gap x.2)

def promote (s : Shape) (rows ell gap : ℕ) (f : Array s rows ell) : Array s rows ell :=
  fun i => coefficient gap (f i)

theorem coefficient_width (gap : ℕ) (x : Coefficient) :
    (coefficient gap x).1.length=x.1.length ∧ (coefficient gap x).2.length=x.2.length :=
  ⟨NativeSignedGapPromoteWord.result_length gap x.1,
    NativeSignedGapPromoteWord.result_length gap x.2⟩

theorem coefficient_promotes (b gap M : ℕ) (x : Coefficient)
    (hw : x.1.length=b+1 ∧ x.2.length=b+1) (hd : gap≤b+1)
    (hb : |ButterflySigned.signedValue b x.1|≤(M:ℤ) ∧
      |ButterflySigned.signedValue b x.2|≤(M:ℤ)) (hg : M*2^gap<2^b) :
    Promotes b gap x (coefficient gap x) :=
  ⟨NativeSignedGapPromoteWord.result_signed_bounded b gap M x.1 hw.1
      (by omega) hb.1 hg,
    NativeSignedGapPromoteWord.result_signed_bounded b gap M x.2 hw.2
      (by omega) hb.2 hg⟩

theorem promotes (s : Shape) (rows ell q n M gap : ℕ) (f : Array s rows ell)
    (hw : Width s rows ell q f) (hg : Grid s rows ell q n M f)
    (hd : gap≤half s q+1) (hguard : M*2^gap<2^(half s q)) (i : _) :
    Promotes (half s q) gap (f i) (promote s rows ell gap f i) := by
  have hwi : (f i).1.length=half s q+1 ∧ (f i).2.length=half s q+1 := by
    simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using hw i
  exact coefficient_promotes _ gap M (f i) hwi hd
    (ButterflyGuard.represented_bound _ _ n M (hg i)) hguard

/-- A concrete bank result, rather than an arbitrary promotion relation. -/
def aligned {ι : Type*} [DecidableEq ι] (s : Shape) (rows ell q : ℕ)
    (rho : Fin s.chunk) {left k : ℕ}
    (visit : CompactComplexRecursiveGeometry.Visit s.active left k)
    (dir : CompactSpectatorLeafGuardOriginal.Direction) (selected : ι)
    (before : ι → Array s rows ell) : ι → Array s rows ell := fun role =>
  if role=selected then CompactSpectatorLeafGuardOriginal.result dir s rows ell q rho visit (before role)
  else promote s rows ell (CompactComplexRecursiveGeometry.arity^k) (before role)

/-- Genuine stopped arithmetic and literal spectator shifts establish the
same physical denominator and preserve every spectator's decoded value. -/
theorem stopped_from_path {ι : Type*} [DecidableEq ι]
    (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk)
    {left k levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path s.active left k levels frames returned)
    (visit : CompactComplexRecursiveGeometry.Visit s.active left k)
    (dir : CompactSpectatorLeafGuardOriginal.Direction) (selected : ι)
    (before : ι → Array s rows ell) (p C n : ℕ) (hp : p≤q)
    (hchunk : dependencyCoefficient C≤s.chunk)
    (hwidth : ∀ role,Width s rows ell q (before role))
    (hbefore : ∀ role,Grid s rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) (before role)) :
    let M := CompactRecursiveGridBudget.bound p C levels (frames+2*returned)
    let gap := CompactComplexRecursiveGeometry.arity^k
    (∀ role,Grid s rows ell q (n+gap) (M*4^gap)
      (aligned s rows ell q rho visit dir selected before role)) ∧
    (∀ role,Grid s rows ell q (n+gap)
      (CompactRecursiveGridBudget.bound p C levels (frames+2*(returned+gap)))
      (aligned s rows ell q rho visit dir selected before role)) ∧
    (∀ role,role≠selected → decoded s rows ell q (n+gap)
      (aligned s rows ell q rho visit dir selected before role)=
        decoded s rows ell q n (before role)) := by
  have hg : CompactComplexRecursiveGeometry.arity^k≤s.bits :=
    CompactSpectatorLeafSemantics.count_le_bits s rho visit
  have hd : CompactComplexRecursiveGeometry.arity^k≤half s q+1 := by
    unfold half ButterflyGuard.halfWidth
    omega
  have hshared := CompactComplexChildGridAlignment.stopped_shared_grid s rows ell q n _ rho visit dir selected before
    (aligned s rows ell q rho visit dir selected before) (hwidth selected) hbefore
    (CompactSpectatorInheritedGrid.guard_from_path s q path p C _ hp hchunk hg)
    (by simp only [aligned,ite_true]) (fun role hr i => by
      simp only [aligned,ite_eq_right hr]
      exact promotes s rows ell q n _ _ (before role) (hwidth role) (hbefore role) hd
        (CompactComplexChildGridAlignment.promotion_capacity_from_path s q path p C _ hp hchunk hg) i)
  refine ⟨hshared.1,?_,hshared.2⟩
  intro role i
  exact Networks.GaussianPrecision.bound_mono
    (CompactComplexChildGridReturnBudget.returned_bound p C levels frames returned _)
    (hshared.1 role i)

end
end IntegerMultBounds.Machine.CompactComplexChildGridPromoted
