module

public import IntegerMultBounds.MathlibTM2.Cover.Fallback
public import Mathlib.LinearAlgebra.Matrix.Transvection

/-! Split the diagonal left by fallback elimination into reciprocal unit pairs and one sign. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
noncomputable section
open Matrix Finset GoodForm
variable {R : Type*} [CommRing R] {n : ℕ}

theorem Elim.det_sign {a s : ℕ} {E : Matrix (Fin n) (Fin n) R} (h : Elim a s E) :
    E.det = 1 ∨ E.det = -1 := by
  induction h with
  | one => exact Or.inl det_one
  | add i k c hik _ ih =>
    have add : 1 + colMat k (Pi.single i c) = transvection i k c := by
      unfold transvection
      congr 1
      ext x y
      by_cases hx : i = x <;> by_cases hy : k = y <;> simp [colMat,single,Pi.single_apply,hx,hy,eq_comm]
    rwa [det_mul,add,det_transvection_of_ne _ _ hik,one_mul]
  | swap i j _ ih =>
    have swap : (swapMat i j : Matrix (Fin n) (Fin n) R) =
        (1 : Matrix (Fin n) (Fin n) R).submatrix (Equiv.swap i j) id := by
      ext x y
      simp [swapMat,one_apply,eq_comm]
    rw [det_mul,swap,det_permute,det_one,mul_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap i j)) with h | h <;>
      rcases ih with e | e <;> simp [h,e]

/-- Balance a unit at coordinate `i+1` by its inverse at coordinate zero. -/
def pair (i : Fin n) (u : Rˣ) : Fin (n+1) → Rˣ :=
  Fin.cons u⁻¹ (fun j => if j = i then u else 1)

theorem unit_pairs (d : Fin (n+1) → Rˣ) :
    d = Fin.cons (∏ j, d j) (fun _ => 1) * ∏ i : Fin n, pair i (d i.succ) := by
  funext j
  induction j using Fin.cases with
  | zero => simp [Pi.mul_apply,Finset.prod_apply,pair,Fin.prod_univ_succ]
  | succ j => simp [Pi.mul_apply,Finset.prod_apply,pair]

/-- For a residual of determinant ±1 the first coordinate needs only a sign after pairing. -/
theorem fallback_pairs [IsLocalRing R] (G : Matrix (Fin (n+1)) (Fin (n+1)) R)
    (hg : G.det = 1 ∨ G.det = -1) :
    ∃ (E : Matrix (Fin (n+1)) (Fin (n+1)) R) (d : Fin n → Rˣ) (s : Rˣ),
      Elim ((n+1)*n) (n+1) E ∧ (s = 1 ∨ s = -1) ∧
      E * G = diagonal (fun j => (((Fin.cons s (fun _ => 1) * ∏ i, pair i (d i) : Fin (n+1) → Rˣ) j : Rˣ) : R)) := by
  have hu : IsUnit G.det := by rcases hg with h | h <;> simp [h]
  obtain ⟨E,x,hE,he,hx⟩ := fallback_form G hu
  let d (i : Fin (n+1)) := (hx i).unit
  have val (i) : (d i : R) = x i := (hx i).unit_spec
  have det := congrArg Matrix.det he
  rw [det_mul,det_diagonal] at det
  have sign : (∏ i, d i) = 1 ∨ (∏ i, d i) = -1 := by
    have hprod : ((∏ i, d i : Rˣ) : R) = ∏ i, x i := by simp [Units.coe_prod,val]
    rcases hE.det_sign with h | h <;> rcases hg with e | e <;>
      simp [h,e] at det <;> first | exact Or.inl (Units.ext (hprod.trans det.symm)) | exact Or.inr (Units.ext (hprod.trans det.symm))
  refine ⟨E,fun i => d i.succ,∏ i, d i,by simpa using hE,sign,?_⟩
  rw [he,← unit_pairs d]
  exact congrArg diagonal (funext fun i => (val i).symm)

/-- An ordinary exchange followed by a weighted ordinary exchange scales the two
fields by reciprocal units. Each exchange uses the same reversal on the later field. -/
theorem pair_children {ι : Type*} [Fintype ι] [DecidableEq ι] (C : Matrix ι ι R)
    (hC : C * C = 1) (u : Rˣ) (s : IntegerMultBounds.Swap.Shear.State ι R) :
    let ordinary (A A' : Matrix ι ι R) (x : IntegerMultBounds.Swap.Shear.State ι R) :=
      M8.Exchange.transform 1 C (Weighted.weighted C A A' (M8.Exchange.transform 1 C x))
    ordinary (diagonal (fun _ => (↑u⁻¹ : R))) (diagonal (fun _ => (u : R))) (ordinary 1 1 s) =
      ((↑u⁻¹ : R) • s.1, (u : R) • s.2) := by
  dsimp only
  rw [ordinary_of_reversed C 1 1 hC,ordinary_of_reversed _ _ _ hC]
  simp only [one_mulVec]
  congr 1 <;> funext i <;> simp [mulVec_diagonal]

theorem rev_mulVec (x : Fin n → R) : M8.ReversedExchange.rev n *ᵥ x = fun i => x i.rev := by
  funext i
  simp [mulVec,dotProduct,M8.ReversedExchange.rev,ite_mul]

theorem reversed_word (x : Fin n → R) :
    List.ofFn (M8.ReversedExchange.rev n *ᵥ x) = (List.ofFn x).reverse := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [rev_mulVec,Fin.rev,Nat.sub_sub,Nat.add_comm]

/-- One unweighted reversed child exchanges and reverses the two halves. A central atom
of an odd-length field stays in place; an even-length field has an empty middle. -/
theorem reversal_child (x y : Fin n → R) (mid : List R) (hm : mid.reverse = mid) :
    let result := Weighted.weighted (M8.ReversedExchange.rev n) 1 1 (x,y)
    List.ofFn result.1 ++ mid ++ List.ofFn result.2 =
      (List.ofFn x ++ mid ++ List.ofFn y).reverse := by
  simp [Weighted.weighted,reversed_word,List.reverse_append,hm,List.append_assoc]

end
end IntegerMultBounds.MathlibTM2.Cover.Fallback
