module

public import IntegerMultBounds.MathlibTM2.Cover.GoodForm
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.Algebra.MvPolynomial.Rename

/-!
# The bad classes are rare

A cover label is bad for a move when some leading principal minor of `g P g⁻¹` of size at most
the rank vanishes in the residue field. `bad_count`: over a finite field with `q` elements, if
one label is good, the number of bad invertible labels times `q` is at most
`(∑_{k ≤ r} k (m + 1)) q^(m²)`. So the bad fraction of the label box is at most
`r (r + 1) (m + 1) / (2 q)`.

Each minor of `X P adj(X)`, for the matrix of variables `X`, is a polynomial of total degree at
most `k (m + 1)` (`totalDegree_minorPoly`). It is nonzero because it does not vanish at the good
label (`eval_minorPoly`, `minor_adjugate`), and a nonzero polynomial of degree `d` has at most
`d q^(N-1)` zeros in `F^N` (`card_zeros_le`, from the Schwartz–Zippel lemma).

The polynomial lemmas repeat those of `M8.GenericBasis`, which are stated over `ℚ`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.BadClass

noncomputable section
open MvPolynomial Matrix Finset
open IntegerMultBounds.MathlibTM2.Cover.GoodForm (lead)

variable {m : ℕ} {F : Type*} [Field F]

/-! ### Zeros of a polynomial over a finite field -/

open scoped Classical in
/-- A nonzero polynomial of total degree `d` in the variables `σ` has at most `d q^(|σ| - 1)`
zeros over a field with `q` elements. -/
theorem card_zeros_le {σ : Type*} [Fintype σ] [DecidableEq σ] [Fintype F] (p : MvPolynomial σ F) (hp : p ≠ 0) :
    #{x : σ → F | eval x p = 0} * Fintype.card F ≤
      p.totalDegree * Fintype.card F ^ Fintype.card σ := by
  have hp' : rename (Fintype.equivFin σ) p ≠ 0 := fun h =>
    hp (rename_injective _ (Fintype.equivFin σ).injective (h.trans (map_zero _).symm))
  have hdeg : (rename (Fintype.equivFin σ) p).totalDegree ≤ p.totalDegree :=
    totalDegree_rename_le _ p
  have hsz := schwartz_zippel_totalDegree hp' (Finset.univ : Finset F)
  have hcard : #{x : σ → F | eval x p = 0} =
      #{f ∈ Fintype.piFinset fun _ : Fin (Fintype.card σ) => (Finset.univ : Finset F) |
        eval f (rename (Fintype.equivFin σ) p) = 0} := by
    refine Finset.card_equiv (Equiv.arrowCongr (Fintype.equivFin σ) (Equiv.refl F)) fun x => ?_
    have hx : (Equiv.arrowCongr (Fintype.equivFin σ) (Equiv.refl F) x) ∘ Fintype.equivFin σ = x := by
      funext a
      simp [Equiv.arrowCongr]
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, implies_true, eval_rename,
      hx]
  have hq : (0 : NNRat) < (#(Finset.univ : Finset F) : NNRat) := by
    rw [Finset.card_univ]
    exact_mod_cast Fintype.card_pos
  rw [← hcard, div_le_div_iff₀ (pow_pos hq _) hq] at hsz
  have hnat : #{x : σ → F | eval x p = 0} * Fintype.card F ≤
      (rename (Fintype.equivFin σ) p).totalDegree * Fintype.card F ^ Fintype.card σ := by
    rw [Finset.card_univ] at hsz
    exact_mod_cast hsz
  exact hnat.trans (Nat.mul_le_mul_right _ hdeg)

/-! ### The minors as polynomials in the label -/

/-- The variables: one per entry of the label. -/
abbrev Var (m : ℕ) := Fin m × Fin m

variable (F) in
/-- The matrix of variables. -/
abbrev X (m : ℕ) : Matrix (Fin m) (Fin m) (MvPolynomial (Var m) F) :=
  mvPolynomialX (Fin m) (Fin m) F

/-- `X P adj(X)`, the conjugate of `P` up to the scalar `det X`. -/
def conj (P : Matrix (Fin m) (Fin m) F) : Matrix (Fin m) (Fin m) (MvPolynomial (Var m) F) :=
  X F m * P.map C * adjugate (X F m)

/-- The leading minor of `X P adj(X)` of size `k`. -/
def minorPoly (P : Matrix (Fin m) (Fin m) F) (k : ℕ) : MvPolynomial (Var m) F :=
  if h : k ≤ m then (lead k h (conj P)).det else 1

/-- The point of a label. -/
def point (g : Matrix (Fin m) (Fin m) F) : Var m → F := fun p => g p.1 p.2

theorem eval_conj (P g : Matrix (Fin m) (Fin m) F) :
    (eval (point g)).mapMatrix (conj P) = g * P * adjugate g := by
  have hP : (eval (point g)).mapMatrix (P.map C) = P := by
    ext a b
    simp
  have hX : (eval (point g)).mapMatrix (X F m) = g := mvPolynomialX_mapMatrix_eval g
  rw [conj, map_mul, map_mul, RingHom.map_adjugate, hX, hP]

theorem eval_minorPoly (P g : Matrix (Fin m) (Fin m) F) (k : ℕ) (h : k ≤ m) :
    eval (point g) (minorPoly P k) = (lead k h (g * P * adjugate g)).det := by
  have hm : minorPoly P k = (lead k h (conj P)).det := by
    simp only [minorPoly, h, ↓reduceDIte]
  rw [hm, RingHom.map_det, ← eval_conj]
  rfl

theorem minor_adjugate (g P : Matrix (Fin m) (Fin m) F) (hg : g.det ≠ 0) (k : ℕ) (h : k ≤ m) :
    (lead k h (g * P * adjugate g)).det = g.det ^ k * (lead k h (g * P * g⁻¹)).det := by
  have hadj : adjugate g = g.det • g⁻¹ := by
    rw [Matrix.inv_def, smul_smul, Ring.inverse_eq_inv', mul_inv_cancel₀ hg, one_smul]
  have hs : lead k h (g.det • (g * P * g⁻¹)) = g.det • lead k h (g * P * g⁻¹) := by
    ext a b
    simp [lead]
  rw [hadj, Matrix.mul_smul, hs, det_smul, Fintype.card_fin]

theorem totalDegree_det_le {n : ℕ} (M : Matrix (Fin n) (Fin n) (MvPolynomial (Var m) F)) (d : ℕ)
    (h : ∀ a b, (M a b).totalDegree ≤ d) : M.det.totalDegree ≤ n * d := by
  rw [det_apply]
  apply totalDegree_finsetSum_le
  intro σ _
  refine (totalDegree_smul_le _ _).trans ?_
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i, (M (σ i) i).totalDegree ≤ ∑ _i : Fin n, d := Finset.sum_le_sum fun i _ => h _ _
    _ = n * d := by simp

theorem totalDegree_X_entry (a b : Fin m) : ((X F m) a b).totalDegree ≤ 1 := by
  show ((mvPolynomialX (Fin m) (Fin m) F) a b).totalDegree ≤ 1
  rw [mvPolynomialX_apply, MvPolynomial.totalDegree_X]

theorem totalDegree_adjugate (a b : Fin m) : (adjugate (X F m) a b).totalDegree ≤ m := by
  rw [adjugate_apply]
  have h := totalDegree_det_le ((X F m).updateRow b (Pi.single a 1)) 1 (by
    intro c e
    by_cases hc : c = b
    · subst hc
      rw [updateRow_self]
      by_cases he : e = a
      · subst he
        simp
      · simp [he]
    · rw [updateRow_ne hc]
      exact totalDegree_X_entry c e)
  simpa using h

theorem totalDegree_conj (P : Matrix (Fin m) (Fin m) F) (a b : Fin m) :
    (conj P a b).totalDegree ≤ m + 1 := by
  rw [conj, mul_apply]
  apply totalDegree_finsetSum_le
  intro l _
  refine (totalDegree_mul _ _).trans ?_
  have h1 : ((X F m * P.map C : Matrix (Fin m) (Fin m) (MvPolynomial (Var m) F)) a l).totalDegree
      ≤ 1 := by
    rw [mul_apply]
    apply totalDegree_finsetSum_le
    intro k _
    refine (totalDegree_mul _ _).trans ?_
    simp [totalDegree_C]
  have h2 := totalDegree_adjugate (F := F) l b
  omega

theorem totalDegree_minorPoly (P : Matrix (Fin m) (Fin m) F) (k : ℕ) :
    (minorPoly P k).totalDegree ≤ k * (m + 1) := by
  rw [minorPoly]
  split_ifs with h
  · exact totalDegree_det_le _ _ fun _ _ => totalDegree_conj P _ _
  · simp

/-- A minor polynomial is nonzero when it does not vanish at one invertible label. -/
theorem minorPoly_ne_zero {P g : Matrix (Fin m) (Fin m) F} (hg : g.det ≠ 0) (k : ℕ) (h : k ≤ m)
    (hgen : (lead k h (g * P * g⁻¹)).det ≠ 0) : minorPoly P k ≠ 0 := by
  intro h0
  have he := eval_minorPoly P g k h
  rw [h0, map_zero, minor_adjugate g P hg] at he
  exact mul_ne_zero (pow_ne_zero _ hg) hgen he.symm

/-! ### The count -/

open scoped Classical in
/-- **The bad classes are rare.** If one invertible label makes the leading minors of sizes
`1..r` of `g P g⁻¹` nonzero, the invertible labels where one of them vanishes number at most
`(∑_{k < r} (k + 1) (m + 1)) q^(m² - 1)`. -/
theorem bad_count [Fintype F] (P : Matrix (Fin m) (Fin m) F) (r : ℕ) (hr : r ≤ m)
    (g₀ : Matrix (Fin m) (Fin m) F) (hg₀ : g₀.det ≠ 0)
    (hgen : ∀ k (hk : k < r), (lead (k + 1) (lt_of_lt_of_le hk hr) (g₀ * P * g₀⁻¹)).det ≠ 0) :
    #{g : Matrix (Fin m) (Fin m) F | g.det ≠ 0 ∧
        ∃ k, ∃ hk : k < r, (lead (k + 1) (lt_of_lt_of_le hk hr) (g * P * g⁻¹)).det = 0} *
      Fintype.card F ≤ (∑ k ∈ range r, (k + 1) * (m + 1)) * Fintype.card F ^ (m * m) := by
  have hsub : (Finset.univ.filter fun g : Matrix (Fin m) (Fin m) F => g.det ≠ 0 ∧
        ∃ k, ∃ hk : k < r, (lead (k + 1) (lt_of_lt_of_le hk hr) (g * P * g⁻¹)).det = 0) ⊆
      (range r).biUnion fun k =>
        ({g : Matrix (Fin m) (Fin m) F | eval (point g) (minorPoly P (k + 1)) = 0} : Finset _) := by
    intro g hg
    obtain ⟨hdet, k, hk, hz⟩ := (mem_filter.mp hg).2
    refine mem_biUnion.mpr ⟨k, mem_range.mpr hk, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    rw [eval_minorPoly P g (k + 1) (lt_of_lt_of_le hk hr), minor_adjugate g P hdet, hz, mul_zero]
  have hone (k : ℕ) (hk : k ∈ range r) :
      #({g : Matrix (Fin m) (Fin m) F | eval (point g) (minorPoly P (k + 1)) = 0} : Finset _) *
        Fintype.card F ≤ (k + 1) * (m + 1) * Fintype.card F ^ (m * m) := by
    have hk' := mem_range.mp hk
    have hne := minorPoly_ne_zero hg₀ (k + 1) (lt_of_lt_of_le hk' hr) (hgen k hk')
    have hz := card_zeros_le (minorPoly P (k + 1)) hne
    have hcard : #({g : Matrix (Fin m) (Fin m) F | eval (point g) (minorPoly P (k + 1)) = 0} :
        Finset _) = #{x : Var m → F | eval x (minorPoly P (k + 1)) = 0} :=
      Finset.card_equiv (Equiv.curry (Fin m) (Fin m) F).symm fun g => by
        simp only [mem_filter, mem_univ, true_and]
        rfl
    rw [hcard]
    refine hz.trans ?_
    have hv : Fintype.card (Var m) = m * m := by simp
    rw [hv]
    exact Nat.mul_le_mul_right _ (totalDegree_minorPoly P (k + 1))
  calc _ ≤ (∑ k ∈ range r,
        #({g : Matrix (Fin m) (Fin m) F | eval (point g) (minorPoly P (k + 1)) = 0} :
          Finset _)) * Fintype.card F :=
        Nat.mul_le_mul_right _ ((card_le_card hsub).trans card_biUnion_le)
    _ = ∑ k ∈ range r,
        #({g : Matrix (Fin m) (Fin m) F | eval (point g) (minorPoly P (k + 1)) = 0} :
          Finset _) * Fintype.card F := Finset.sum_mul _ _ _
    _ ≤ ∑ k ∈ range r, (k + 1) * (m + 1) * Fintype.card F ^ (m * m) := Finset.sum_le_sum hone
    _ = _ := (Finset.sum_mul _ _ _).symm

end

end IntegerMultBounds.MathlibTM2.Cover.BadClass
