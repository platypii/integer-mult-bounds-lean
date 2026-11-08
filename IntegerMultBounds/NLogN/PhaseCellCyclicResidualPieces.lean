module

public import IntegerMultBounds.NLogN.PhaseCellCyclicInteriorSplit
public import IntegerMultBounds.NLogN.PhaseCellCyclicPrincipalStability

/-! Joint cyclic residuals are assembled by selecting physical rows, without addition. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
open scoped BigOperators
open Finset PhaseCellMatrix SchurDominance
variable {s t : ℕ} [NeZero s]

theorem haloInterior_column_support (p u a b : ℕ) (hb : b ≤ s) (i j : ZMod s)
    (hj : j ∈ haloInterior s t (PhaseCellBand.width p u) a b)
    (hne : realMatrix s t p u i j ≠ 0) : i ∈ haloVertices s a b := by
  obtain ⟨_,hlo,hhi⟩ := mem_filter.mp hj
  obtain ⟨delta,hdlo,hdhi,he⟩ := realMatrix_support p u i j hne
  have hi : i = (((j.val : ℤ)-delta : ℤ) : ZMod s) := by rw [← he]; simp
  have hval : (i.val : ℤ) = (j.val : ℤ)-delta := by
    rw [hi,ZMod.val_intCast,Int.emod_eq_of_lt (by omega) (by omega)]
  apply (mem_haloVertices a b i).mpr
  constructor <;> omega

theorem cyclicPrincipal_piece_cross_interior_zero (p u a n : ℕ) (ha : a < s) (hn : n ≤ s) :
    (∀ i ∈ haloVertices s a (a+min n (s-a)),
      ∀ j ∈ haloInterior s t (PhaseCellBand.width p u) 0 (n-min n (s-a)),
        realMatrix s t p u i j = 0) ∧
    (∀ i ∈ haloVertices s 0 (n-min n (s-a)),
      ∀ j ∈ haloInterior s t (PhaseCellBand.width p u) a (a+min n (s-a)),
        realMatrix s t p u i j = 0) := by
  have hd := cyclicPrincipalPieces_disjoint a n ha hn
  constructor
  · intro i hi j hj
    by_contra hne
    exact disjoint_left.mp hd hi (haloInterior_column_support p u 0 _ (by omega) i j hj hne)
  · intro i hi j hj
    by_contra hne
    exact disjoint_left.mp hd (haloInterior_column_support p u a _ (by omega) i j hj hne) hi

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

namespace IntegerMultBounds.NLogN.SchurDominance
open scoped BigOperators
open Finset
variable {iota : Type*} [DecidableEq iota]

theorem residual_union_eq_left_of_zero (M : Matrix iota iota ℝ) (I J : Finset iota)
    (hdisj : Disjoint I J) (R S : (iota → ℝ) → iota → ℝ) (rhs : iota → ℝ) (i : iota)
    (hzero : ∀ k ∈ J, M i k = 0) :
    residual M (I∪J) (fun b k => if k ∈ I then R b k else S b k) rhs i =
      residual M I R rhs i := by
  rw [residual_union_of_piecewise M I J hdisj R S rhs i]
  have hJ : residual M J S rhs i = rhs i := by
    simp only [residual]
    rw [sum_eq_zero (fun k hk => by rw [hzero k hk,zero_mul]),sub_zero]
  rw [hJ]
  ring

theorem residual_union_eq_right_of_zero (M : Matrix iota iota ℝ) (I J : Finset iota)
    (hdisj : Disjoint I J) (R S : (iota → ℝ) → iota → ℝ) (rhs : iota → ℝ) (i : iota)
    (hzero : ∀ k ∈ I, M i k = 0) :
    residual M (I∪J) (fun b k => if k ∈ I then R b k else S b k) rhs i =
      residual M J S rhs i := by
  rw [residual_union_of_piecewise M I J hdisj R S rhs i]
  have hI : residual M I R rhs i = rhs i := by
    simp only [residual]
    rw [sum_eq_zero (fun k hk => by rw [hzero k hk,zero_mul]),sub_zero]
  rw [hI]
  ring

end IntegerMultBounds.NLogN.SchurDominance

namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
open Finset PhaseCellMatrix SchurDominance
variable {s t : ℕ} [NeZero s]

theorem cyclicPrincipal_residual_pieces (p u a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (R S : (ZMod s → ℝ) → ZMod s → ℝ) (rhs : ZMod s → ℝ)
    (i : ZMod s) (hi : i ∈ cyclicPrincipalVertices s a n) :
    residual (realMatrix s t p u) (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n)
      (fun b k => if k ∈ haloInterior s t (PhaseCellBand.width p u) a (a+min n (s-a))
        then R b k else S b k) rhs i =
      if i ∈ haloVertices s a (a+min n (s-a)) then
        residual (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a (a+min n (s-a))) R rhs i
      else residual (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) 0 (n-min n (s-a))) S rhs i := by
  have hd := (cyclicPrincipalPieces_disjoint a n ha hn).mono
    (haloInterior_subset s t (PhaseCellBand.width p u) a _) (haloInterior_subset s t (PhaseCellBand.width p u) 0 _)
  have hz := cyclicPrincipal_piece_cross_interior_zero (t := t) p u a n ha hn
  by_cases hleft : i ∈ haloVertices s a (a+min n (s-a))
  · rw [ite_eq_left hleft]
    exact residual_union_eq_left_of_zero _ _ _ hd R S rhs i (hz.1 i hleft)
  · rw [ite_eq_right hleft]
    have hright : i ∈ haloVertices s 0 (n-min n (s-a)) := (mem_union.mp hi).resolve_left hleft
    exact residual_union_eq_right_of_zero _ _ _ hd R S rhs i (hz.2 i hright)

/-- Selecting the two physical residual rows retains the original error budget. -/
theorem cyclicPrincipal_residual_pieces_error (p u a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (R S : (ZMod s → ℝ) → ZMod s → ℝ) (rhs left right : ZMod s → ℝ) (E : ℝ)
    (hleft : ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a (a+min n (s-a)),
      |left i-residual (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a (a+min n (s-a))) R rhs i| ≤ E)
    (hright : ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) 0 (n-min n (s-a)),
      |right i-residual (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) 0 (n-min n (s-a))) S rhs i| ≤ E) :
    ∀ i ∈ cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n,
      |(if i ∈ haloVertices s a (a+min n (s-a)) then left i else right i)-
        residual (realMatrix s t p u) (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n)
          (fun b k => if k ∈ haloInterior s t (PhaseCellBand.width p u) a (a+min n (s-a))
            then R b k else S b k) rhs i| ≤ E := by
  intro i hi
  have hv := (mem_sdiff.mp hi).1
  rw [cyclicPrincipal_residual_pieces p u a n ha hn R S rhs i hv]
  rw [cyclicPrincipalBoundary_eq t (PhaseCellBand.width p u) a n ha hn] at hi
  by_cases hmem : i ∈ haloVertices s a (a+min n (s-a))
  · simp only [ite_eq_left hmem]
    apply hleft i
    rcases mem_union.mp hi with h | h
    · exact h
    · exact False.elim (disjoint_left.mp (cyclicPrincipalPieces_disjoint a n ha hn)
        hmem (mem_sdiff.mp h).1)
  · simp only [ite_eq_right hmem]
    apply hright i
    rcases mem_union.mp hi with h | h
    · exact False.elim (hmem (mem_sdiff.mp h).1)
    · exact h

/-- One joint Schur column from two interval residual passes, with no extra error loss. -/
theorem cyclicPrincipal_schur_column_pieces_error (hst : s < t) {alpha gap : ℝ} (halpha : 0 < alpha)
    (p u a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hsquare : alpha^2 = (u : ℝ))
    (htheta : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ gap*((t : ℝ)/s-1)) (hbudget : alpha^2*gap ≤ p)
    (R S : (ZMod s → ℝ) → ZMod s → ℝ)
    (hR : ∀ rhs, Solves (realMatrix s t p u)
      (haloInterior s t (PhaseCellBand.width p u) a (a+min n (s-a))) (R rhs) rhs)
    (hS : ∀ rhs, Solves (realMatrix s t p u)
      (haloInterior s t (PhaseCellBand.width p u) 0 (n-min n (s-a))) (S rhs) rhs)
    (j : ZMod s) (hj : j ∈ cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n)
    (c left right : ZMod s → ℝ) (eta E : ℝ) (heta : 0 ≤ eta)
    (hcolumn : ∀ k ∈ cyclicPrincipalVertices s a n, |c k-realMatrix s t p u k j| ≤ eta)
    (hleft : ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a (a+min n (s-a)),
      |left i-residual (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a (a+min n (s-a))) R c i| ≤ E)
    (hright : ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) 0 (n-min n (s-a)),
      |right i-residual (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) 0 (n-min n (s-a))) S c i| ≤ E) :
    ∀ i ∈ cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n,
      |(if i ∈ haloVertices s a (a+min n (s-a)) then left i else right i)-
        (SchurDominance.run (realMatrix s t p u) (cyclicPrincipalVertices s a n)
          (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n).toList).1 i j| ≤ E+(1+16*(p : ℝ))*eta := by
  exact cyclicPrincipal_schur_column_error hst halpha p u a n hp hwidth hsquare htheta hgap hbudget
    _ (cyclicPrincipalInterior_solver p u a n ha hn R S hR hS) j hj c _ eta E heta hcolumn
    (cyclicPrincipal_residual_pieces_error p u a n ha hn R S c left right E hleft hright)

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
