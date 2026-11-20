module

public import IntegerMultBounds.MathlibTM2.Cover.LabelProjector
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Projection

/-! In a basis beginning with its image, a projector fixes its first rank-many columns. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.LabelProjector
open Matrix Finset
open IntegerMultBounds.Swap.LowerTriangular (Factorization)
open IntegerMultBounds.Swap.Modular
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
local instance : Fact prime.Prime := ⟨prime_prime⟩

theorem residue_rank {m : ℕ} (P : Matrix (Fin m) (Fin m) ℚ) (f : Factorization univ univ P)
    (hd : ∀ d ∈ factorizationDenominators f, d < prime) : (reduce prime P).rank = P.rank := by
  have reduced := reduce_factorization_of_prime f prime_prime hd 1
  generalize h : prime ^ 1 = q at reduced
  have eq : q = prime := h.symm.trans (pow_one _)
  rw [eq] at reduced
  obtain ⟨count,_,_,_,_,left,_,_,right,factors⟩ := reduced
  rw [factors,rank_mul_eq_left_of_isUnit_det _ _ (isUnit_det_of_left_inverse right),
    rank_mul_eq_right_of_isUnit_det _ _ (isUnit_det_of_right_inverse left),
    IntegerMultBounds.Swap.PivotRank.rank_pivotMatrix _ f.nodup₁ f.nodup₂,count]

theorem exists_good_basis {F : Type*} [Field F] {m : ℕ} (P : Matrix (Fin m) (Fin m) F)
    (idem : P*P = P) (r : ℕ) (rank : P.rank = r) (fits : r ≤ m) :
    ∃ g : Matrix (Fin m) (Fin m) F, g.det ≠ 0 ∧ ∀ k (hk : k < r),
      (GoodForm.lead (k+1) (lt_of_lt_of_le hk fits) (g*P*g⁻¹)).det ≠ 0 := by
  classical
  let f := P.mulVecLin
  have proj : IsIdempotentElem f := by
    change P.mulVecLin.comp P.mulVecLin = P.mulVecLin
    rw [← Matrix.mulVecLin_mul,idem]
  let b₁ := Module.finBasisOfFinrankEq F (LinearMap.range f) rank
  let b₂ := Module.finBasis F (LinearMap.ker f)
  have size : r + Module.finrank F (LinearMap.ker f) = m := by
    rw [← rank]
    simpa [Matrix.rank,f] using f.finrank_range_add_finrank_ker
  let e := finSumFinEquiv.trans (finCongr size)
  let b := (((b₁.prod b₂).map (Submodule.prodEquivOfIsCompl _ _ (LinearMap.IsIdempotentElem.isCompl (f := f) proj))).reindex e)
  let std := Pi.basisFun F (Fin m)
  let g := b.toMatrix std
  have fixed (i : Fin r) : f (b (e (.inl i))) = b (e (.inl i)) := by
    apply (LinearMap.IsIdempotentElem.mem_range_iff (p := f) proj).mp
    simp [b]
  have repr : g*P*g⁻¹ = LinearMap.toMatrix b b f := by
    rw [show g⁻¹ = std.toMatrix b from Matrix.inv_eq_left_inv (std.toMatrix_mul_toMatrix_flip b)]
    change b.toMatrix std * P * std.toMatrix b = _
    rw [basis_toMatrix_mul b std std P,linearMap_toMatrix_mul_basis_toMatrix]
    rfl
  refine ⟨g,(isUnit_det_of_right_inverse (b.toMatrix_mul_toMatrix_flip std)).ne_zero,?_⟩
  intro k hk
  have block : GoodForm.lead (k+1) (lt_of_lt_of_le hk fits) (g*P*g⁻¹) = 1 := by
    ext i j
    let j' : Fin r := j.castLE hk
    have col : j.castLE (lt_of_lt_of_le hk fits) = e (.inl j') := Fin.ext rfl
    rw [repr]
    rw [GoodForm.lead,Matrix.submatrix_apply,LinearMap.toMatrix_apply]
    rw [col,fixed,← col]
    simp [Matrix.one_apply,Module.Basis.repr_self, Finsupp.single_apply,eq_comm]
  rw [block,Matrix.det_one]
  exact one_ne_zero

theorem residue_witness {m w : ℕ} (hw : 0 < w) (P : Matrix (Fin m) (Fin m) ℚ)
    (idem : P*P = P) (f : Factorization univ univ P)
    (hd : ∀ d ∈ factorizationDenominators f, d < prime) (fits : P.rank ≤ m) :
    ∃ g : Matrix (Fin m) (Fin m) (ZMod prime), g.det ≠ 0 ∧ ∀ k (hk : k < P.rank),
      (GoodForm.lead (k+1) (lt_of_lt_of_le hk fits)
        (g*(LabelRing.res prime w hw).mapMatrix (reduce (prime^w) P)*g⁻¹)).det ≠ 0 := by
  have adm : Admissible prime P := by
    simpa using admissible_of_lt prime_prime
      (fun d (h : d ∈ denominators P) => hd d (by simp [factorizationDenominators,h])) 1
  rw [residue_reduce hw P adm]
  apply exists_good_basis _ _ _ (residue_rank P f hd) fits
  rw [← reduce_mul _ adm adm,idem]

end IntegerMultBounds.MathlibTM2.Cover.LabelProjector
