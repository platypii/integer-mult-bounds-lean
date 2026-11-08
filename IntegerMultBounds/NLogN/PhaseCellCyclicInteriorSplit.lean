module

public import IntegerMultBounds.NLogN.PhaseCellCyclicPrincipalGeometry
public import IntegerMultBounds.NLogN.SchurSolve

/-! Guarded physical interiors can be solved separately inside one cyclic principal system. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
open scoped BigOperators
open Finset PhaseCellMatrix SchurDominance
variable {s t : ℕ} [NeZero s]

theorem haloInterior_row_support (p u a b : ℕ) (hb : b ≤ s) (i j : ZMod s)
    (hi : i ∈ haloInterior s t (PhaseCellBand.width p u) a b) (hne : realMatrix s t p u i j ≠ 0) :
    j ∈ haloVertices s a b := by
  obtain ⟨_,hlo,hhi⟩ := mem_filter.mp hi
  obtain ⟨delta,hdlo,hdhi,he⟩ := realMatrix_support p u i j hne
  have hj : j = (((i.val : ℤ)+delta : ℤ) : ZMod s) := by rw [← he]; simp
  have hval : (j.val : ℤ) = (i.val : ℤ)+delta := by
    rw [hj,ZMod.val_intCast,Int.emod_eq_of_lt (by omega) (by omega)]
  apply (mem_haloVertices a b j).mpr
  constructor <;> omega

theorem cyclicPrincipal_interiors_uncoupled (p u a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (i j : ZMod s)
    (hi : i ∈ haloInterior s t (PhaseCellBand.width p u) a (a+min n (s-a)))
    (hj : j ∈ haloInterior s t (PhaseCellBand.width p u) 0 (n-min n (s-a))) :
    realMatrix s t p u i j = 0 ∧ realMatrix s t p u j i = 0 := by
  have hdisj := cyclicPrincipalPieces_disjoint a n ha hn
  constructor
  · by_contra hne
    exact disjoint_left.mp hdisj
      (haloInterior_row_support p u a _ (by omega) i j hi hne)
      (haloInterior_subset s t _ 0 _ hj)
  · by_contra hne
    exact disjoint_left.mp hdisj (haloInterior_subset s t _ a _ hi)
      (haloInterior_row_support p u 0 _ (by omega) j i hj hne)

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

namespace IntegerMultBounds.NLogN.SchurDominance
open scoped BigOperators
open Finset
variable {iota : Type*} [DecidableEq iota]

theorem solves_union_of_cross_zero (M : Matrix iota iota ℝ) (I J : Finset iota) (hdisj : Disjoint I J)
    (hcross : ∀ i ∈ I, ∀ j ∈ J, M i j = 0 ∧ M j i = 0)
    (x y rhs : iota → ℝ) (hx : Solves M I x rhs) (hy : Solves M J y rhs) :
    Solves M (I∪J) (fun k => if k ∈ I then x k else y k) rhs := by
  intro i hi
  rw [sum_union hdisj]
  rcases mem_union.mp hi with hi | hi
  · have hI : (∑ k ∈ I, M i k*(if k ∈ I then x k else y k)) = ∑ k ∈ I, M i k*x k := by
      apply sum_congr rfl
      intro k hk
      rw [ite_eq_left hk]
    have hJ : (∑ k ∈ J, M i k*(if k ∈ I then x k else y k)) = 0 :=
      sum_eq_zero (fun k hk => by rw [(hcross i hi k hk).1,zero_mul])
    rw [hI,hJ,add_zero]
    exact hx i hi
  · have hI : (∑ k ∈ I, M i k*(if k ∈ I then x k else y k)) = 0 :=
      sum_eq_zero (fun k hk => by rw [(hcross k hk i hi).2,zero_mul])
    have hJ : (∑ k ∈ J, M i k*(if k ∈ I then x k else y k)) = ∑ k ∈ J, M i k*y k := by
      apply sum_congr rfl
      intro k hk
      have hnot : k ∉ I := fun hh => disjoint_left.mp hdisj hh hk
      rw [ite_eq_right hnot]
    rw [hI,hJ,zero_add]
    exact hy i hi

theorem residual_union_of_piecewise (M : Matrix iota iota ℝ) (I J : Finset iota) (hdisj : Disjoint I J)
    (R S : (iota → ℝ) → iota → ℝ) (rhs : iota → ℝ) (i : iota) :
    residual M (I∪J) (fun b k => if k ∈ I then R b k else S b k) rhs i =
      residual M I R rhs i+residual M J S rhs i-rhs i := by
  have hI : (∑ k ∈ I, M i k*(if k ∈ I then R rhs k else S rhs k)) = ∑ k ∈ I, M i k*R rhs k := by
    apply sum_congr rfl
    intro k hk
    rw [ite_eq_left hk]
  have hJ : (∑ k ∈ J, M i k*(if k ∈ I then R rhs k else S rhs k)) = ∑ k ∈ J, M i k*S rhs k := by
    apply sum_congr rfl
    intro k hk
    have hnot : k ∉ I := fun hi => disjoint_left.mp hdisj hi hk
    rw [ite_eq_right hnot]
  simp only [residual,sum_union hdisj,hI,hJ]
  ring

theorem residual_union_error (M : Matrix iota iota ℝ) (I J : Finset iota) (hdisj : Disjoint I J)
    (R S : (iota → ℝ) → iota → ℝ) (rhs left right : iota → ℝ) (i : iota)
    (eLeft eRight : ℝ)
    (hleft : |left i-residual M I R rhs i| ≤ eLeft)
    (hright : |right i-residual M J S rhs i| ≤ eRight) :
    |(left i+right i-rhs i)-residual M (I∪J)
      (fun b k => if k ∈ I then R b k else S b k) rhs i| ≤ eLeft+eRight := by
  rw [residual_union_of_piecewise M I J hdisj R S rhs i]
  have he : (left i+right i-rhs i)-(residual M I R rhs i+residual M J S rhs i-rhs i) =
      (left i-residual M I R rhs i)+(right i-residual M J S rhs i) := by ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hleft hright)

end IntegerMultBounds.NLogN.SchurDominance

namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
open Finset PhaseCellMatrix SchurDominance
variable {s t : ℕ} [NeZero s]

theorem cyclicPrincipalInterior_solves (p u a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (x y rhs : ZMod s → ℝ)
    (hx : Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a (a+min n (s-a))) x rhs)
    (hy : Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) 0 (n-min n (s-a))) y rhs) :
    Solves (realMatrix s t p u) (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n)
      (fun k => if k ∈ haloInterior s t (PhaseCellBand.width p u) a (a+min n (s-a)) then x k else y k) rhs := by
  have hd := (cyclicPrincipalPieces_disjoint a n ha hn).mono
    (haloInterior_subset s t (PhaseCellBand.width p u) a _) (haloInterior_subset s t (PhaseCellBand.width p u) 0 _)
  exact solves_union_of_cross_zero _ _ _ hd
    (fun i hi j hj => cyclicPrincipal_interiors_uncoupled p u a n ha hn i j hi hj) x y rhs hx hy

theorem cyclicPrincipalInterior_solver (p u a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (R S : (ZMod s → ℝ) → ZMod s → ℝ)
    (hR : ∀ rhs, Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a (a+min n (s-a))) (R rhs) rhs)
    (hS : ∀ rhs, Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) 0 (n-min n (s-a))) (S rhs) rhs) :
    ∀ rhs, Solves (realMatrix s t p u) (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n)
      (fun k => if k ∈ haloInterior s t (PhaseCellBand.width p u) a (a+min n (s-a)) then R rhs k else S rhs k) rhs :=
  fun rhs => cyclicPrincipalInterior_solves p u a n ha hn (R rhs) (S rhs) rhs (hR rhs) (hS rhs)

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
