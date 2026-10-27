module

public import IntegerMultBounds.NLogN.ToeplitzInverse
public import IntegerMultBounds.NLogN.SchurSolve

/-! Exact interior solvers. A dominance margin on a finite active set gives an
actual solver for every right-hand side. On a block of the active set closed
under its couplings, whose entries are a diagonal similarity `d_a g(|a-k|)/d_k`
of a symmetric Toeplitz matrix, every solution is the scaled Toeplitz inverse
`x(e a) = d_a Σ_k m a k c(e k)/d_k`. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.SchurDominance

open scoped BigOperators
open Finset

/-- Dominance yields an exact solver for every right-hand side. -/
theorem exists_solver {ι : Type*} [DecidableEq ι] (A : Matrix ι ι ℝ)
    (S : Finset ι) (μ : ℝ) (hμ : 0<μ) (hA : DominatesOn A S μ) :
    ∃ R : (ι → ℝ) → ι → ℝ, ∀ c, Solves A S (R c) c := by
  let M : Matrix S S ℝ := fun i j => A i j
  let ext : (S → ℝ) → ι → ℝ := fun v i => if h : i∈S then v ⟨i, h⟩ else 0
  have hsum (v : S → ℝ) (i : ι) : ∑ j∈S, A i j*ext v j=∑ j : S, A i j*v j := by
    rw [←sum_coe_sort S]
    exact Fintype.sum_congr _ _ fun j => by simp [ext, j.2]
  have hinj : Function.Injective M.mulVec := by
    intro v v' hvv
    have hsol (w : S → ℝ) : Solves A S (ext w) (ext (M.mulVec w)) := by
      intro i hi
      rw [hsum]
      simp [ext, hi, M, Matrix.mulVec, dotProduct]
    funext i
    have h := solves_unique A S μ hμ hA _ _ _ (hsol v) (hvv ▸ hsol v') i i.2
    simpa [ext, i.2] using h
  have hsurj : Function.Surjective M.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  refine ⟨fun c => ext (Classical.choose (hsurj fun i => c i)), fun c i hi => ?_⟩
  rw [hsum]
  have h := congrFun (Classical.choose_spec (hsurj fun i : S => c i)) ⟨i, hi⟩
  simpa [M, Matrix.mulVec, dotProduct] using h

/-- On a closed Toeplitz-similarity block, solutions are the scaled inverse. -/
theorem local_toeplitz {ι : Type*} [DecidableEq ι] (A : Matrix ι ι ℝ) (I : Finset ι)
    (x c : ι → ℝ) (hx : Solves A I x c) (L : ℕ) (e : ℕ → ι)
    (he : ∀ k<L, e k∈I) (hinj : ∀ a<L, ∀ k<L, e a=e k → a=k)
    (hclosed : ∀ a<L, ∀ j∈I, A (e a) j≠0 → ∃ k<L, e k=j)
    (d : ℕ → ℝ) (hd : ∀ k<L, d k≠0) (g : ℕ → ℝ) (m : ℕ → ℕ → ℝ)
    (hm : ToeplitzInverse.IsInverse L g m)
    (hA : ∀ a<L, ∀ k<L, A (e a) (e k)=d a*g (ToeplitzInverse.gap a k)/d k)
    (a : ℕ) (ha : a<L) :
    x (e a)=d a*∑ k∈range L, m a k*(c (e k)/d k) := by
  -- Restrict every active row of the block to the block itself.
  have hrow (b : ℕ) (hb : b<L) :
      ∑ k∈range L, g (ToeplitzInverse.gap b k)*(x (e k)/d k)=c (e b)/d b := by
    have hsub : ∑ j∈I, A (e b) j*x j=∑ j∈(range L).image e, A (e b) j*x j := by
      refine (sum_subset (fun j hj => ?_) fun j hjI hj => ?_).symm
      · obtain ⟨k, hk, rfl⟩ := mem_image.mp hj
        exact he k (mem_range.mp hk)
      · by_contra hne
        obtain ⟨k, hk, rfl⟩ := hclosed b hb j hjI (left_ne_zero_of_mul hne)
        exact hj (mem_image.mpr ⟨k, mem_range.mpr hk, rfl⟩)
    have himg : ∑ j∈(range L).image e, A (e b) j*x j=∑ k∈range L, A (e b) (e k)*x (e k) :=
      sum_image fun k hk k' hk' h => hinj k (mem_range.mp hk) k' (mem_range.mp hk') h
    have h := hx (e b) (he b hb)
    rw [hsub, himg] at h
    rw [eq_div_iff (hd b hb), sum_mul]
    rw [←h]
    refine sum_congr rfl fun k hk => ?_
    rw [hA b hb k (mem_range.mp hk)]
    field_simp [hd k (mem_range.mp hk)]
  have hrec := ToeplitzInverse.recover hm (fun k => x (e k)/d k) a ha
  rw [sum_congr rfl fun l hl => by rw [hrow l (mem_range.mp hl)]] at hrec
  rw [←hrec]
  field_simp [hd a ha]

end IntegerMultBounds.NLogN.SchurDominance
