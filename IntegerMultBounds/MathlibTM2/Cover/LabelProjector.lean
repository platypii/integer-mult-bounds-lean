module

public import IntegerMultBounds.MathlibTM2.Cover.LabelStock
public import IntegerMultBounds.Swap.Modular

/-! Rank factors and the leading-minor test for the projector at a physical label. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.LabelProjector
noncomputable section
open Matrix Finset
open IntegerMultBounds.Swap.Shear (pivotMatrix)
open IntegerMultBounds.Swap.LowerTriangular (Factorization)
open IntegerMultBounds.Swap.Modular (reduce factorizationDenominators reduce_factorization_of_prime)
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open GoodForm (lead)

private theorem pivot_factors {R : Type*} [CommRing R] {m : ℕ}
    (ps : List (Fin m × Fin m)) :
    ∃ (A : Matrix (Fin m) (Fin ps.length) R) (B : Matrix (Fin ps.length) (Fin m) R),
      pivotMatrix ps = A * B := by
  induction ps with
  | nil => exact ⟨0,0,by simp [pivotMatrix]⟩
  | cons p ps ih =>
    obtain ⟨A,B,h⟩ := ih
    refine ⟨fun i => Fin.cons (if i = p.1 then 1 else 0) (A i),
      fun k j => Fin.cons (α := fun _ => R) (if j = p.2 then 1 else 0) (fun t => B t j) k,?_⟩
    ext i j
    rw [pivotMatrix,Matrix.add_apply,h]
    change _ = ∑ k : Fin (ps.length+1), Fin.cons (α := fun _ => R) (if i = p.1 then 1 else 0) (A i) k * Fin.cons (α := fun _ => R) (if j = p.2 then 1 else 0) (fun t => B t j) k
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,Matrix.mul_apply,Matrix.single,Matrix.of_apply]
    by_cases hi : i = p.1 <;> by_cases hj : j = p.2 <;> simp [hi,hj,eq_comm]

/-- Reducing the rational pivot factorization gives rank-sized factors over every admissible
prime power. Conjugation changes only the outside factors. -/
theorem rank_factors {m : ℕ} (P : Matrix (Fin m) (Fin m) ℚ)
    (f : Factorization univ univ P) {q : ℕ} (hq : q.Prime)
    (hd : ∀ d ∈ factorizationDenominators f, d < q) (w : ℕ)
    (g : Matrix (Fin m) (Fin m) (ZMod (q^w))) :
    ∃ (A : Matrix (Fin m) (Fin P.rank) (ZMod (q^w))) (B : Matrix (Fin P.rank) (Fin m) (ZMod (q^w))),
      g * reduce (q^w) P * g⁻¹ = A * B := by
  obtain ⟨hr,_,_,_,_,_,_,_,_,hP⟩ := reduce_factorization_of_prime f hq hd w
  rw [← hr]
  obtain ⟨A,B,h⟩ := pivot_factors (R := ZMod (q^w)) f.L
  refine ⟨g * reduce (q^w) f.E₁ * A,B * reduce (q^w) f.E₂ * g⁻¹,?_⟩
  rw [hP,h]
  simp only [Matrix.mul_assoc]

/-- The finite branch predicate used by the label traversal. -/
def good {m : ℕ} (P : Matrix (Fin m) (Fin m) (ZMod prime)) (r : ℕ) (hr : r ≤ m)
    (g : Matrix (Fin m) (Fin m) (ZMod prime)) : Bool :=
  decide (∀ k : Fin r, (lead (k.val+1) (lt_of_lt_of_le k.isLt hr) (g * P * g⁻¹)).det ≠ 0)

local instance : Fact prime.Prime := ⟨prime_prime⟩
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos w).ne'⟩

theorem good_at {m w : ℕ} (hw : 0 < w) (P g : LabelPadding.Label m w) (hg : IsUnit g.det)
    (r : ℕ) (hr : r ≤ m) (p : ℕ) :
    good ((LabelRing.res prime w hw).mapMatrix P) r hr
      (LabelStock.residue m w 1 (p*(prime^w)^(m*m)+(LabelAddress.address g).val)) = true ↔
      ∀ k (hk : k < r), IsUnit (lead (k+1) (lt_of_lt_of_le hk hr) (g * P * g⁻¹)).det := by
  have res := LabelStock.residue_at hw p 1 0 (by decide) g
  simp only [Nat.mul_one,Nat.add_zero] at res
  rw [res,good,decide_eq_true_eq,Fin.forall_iff]
  simp only [LabelRing.lead_unit_iff prime w hw,LabelRing.res_conj prime w hw g P hg]

open IntegerMultBounds.Swap.Modular (Admissible admissible_of_lt reduce_mul)
open IntegerMultBounds.MathlibTM2.M8.Exchange (transform cross)
open IntegerMultBounds.MathlibTM2.M8.ReversedExchange (rev revExchangeOf)
open IntegerMultBounds.Swap.Shear (State)

/-- A single residue projector supplies the finite branch table at every positive atom width. -/
theorem residue_reduce {m w : ℕ} (hw : 0 < w) (P : Matrix (Fin m) (Fin m) ℚ)
    (adm : Admissible prime P) :
    (LabelRing.res prime w hw).mapMatrix (reduce (prime^w) P) = reduce prime P := by
  ext i j
  apply IntegerMultBounds.Swap.Modular.ratMod_unique prime (adm i j)
  have h := congrArg (LabelRing.res prime w hw)
    (IntegerMultBounds.Swap.Modular.ratMod_mul_den (prime^w) ((adm i j).pow_right w))
  change (LabelRing.res prime w hw) (IntegerMultBounds.Swap.Modular.ratMod (prime^w) (P i j)) * _ = _
  simpa only [map_mul,map_natCast,map_intCast] using h

/-- At an accepted live record, the rational projector acts by the weighted good child. -/
theorem good_move_at {m w : ℕ} (hw : 0 < w) (P : Matrix (Fin m) (Fin m) ℚ)
    (hidem : P * P = P) (f : Factorization univ univ P)
    (hd : ∀ d ∈ factorizationDenominators f, d < prime) (hr : P.rank ≤ m)
    (g : LabelPadding.Label m w) (hg : IsUnit g.det) (p : ℕ)
    (α α' : Fin m → ZMod (prime^w)) (hα : ∀ i, α i * α' i = 1) :
    let M := reduce (prime^w) P
    good (reduce prime P) P.rank hr
      (LabelStock.residue m w 1 (p*(prime^w)^(m*m)+(LabelAddress.address g).val)) = true →
    ∃ (L L' R R' K : LabelPadding.Label m w) (δ δ' : Fin m → ZMod (prime^w)),
      GoodForm.UnitLower L ∧ GoodForm.UnitLower L' ∧ GoodForm.UnitLower R ∧ GoodForm.UnitLower R' ∧
      (∀ i, δ i * δ' i = 1) ∧ ∀ s : State (Fin m) (ZMod (prime^w)),
        transform (diagonal α * L * diagonal α') R'
          (cross (-K) (Weighted.child P.rank (fun i => α i * δ i) (fun i => α' i * δ' i)
            (cross K (transform (diagonal α * L' * diagonal α') R s)))) =
          transform (diagonal α) 1 (revExchangeOf (rev m) (g * M * g⁻¹) (transform (diagonal α') 1 s)) := by
  intro M accepted
  obtain ⟨A,B,hP⟩ := rank_factors P f prime_prime hd w g
  have admissible (e : ℕ) : Admissible (prime^e) P := admissible_of_lt prime_prime
    (fun d h => hd d (by simp [factorizationDenominators,h])) e
  have residue := residue_reduce hw P (by simpa using admissible 1)
  rw [← residue] at accepted
  have adm := admissible w
  have hm : M * M = M := by rw [← reduce_mul _ adm adm,hidem]
  have idempotent : (g * M * g⁻¹) * (g * M * g⁻¹) = g * M * g⁻¹ := by
    calc
      _ = g * (M * (g⁻¹ * g) * M) * g⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.nonsing_inv_mul g hg, Matrix.mul_one,hm]
  exact GoodForm.good_move _ idempotent P.rank hr A B hP ((good_at hw M g hg P.rank hr p).mp accepted) α α' hα

end
end IntegerMultBounds.MathlibTM2.Cover.LabelProjector
