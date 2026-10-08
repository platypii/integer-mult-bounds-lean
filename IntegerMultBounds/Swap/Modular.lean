import IntegerMultBounds.Swap.PivotRank
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Prime.Infinite

/-! Specialization of rational identities to `ℤ/mℤ` (§4, Lemma 4.2). Rationals
whose denominators are prime to `m` form a subring of `ℚ`, and `num · den⁻¹` is
a ring homomorphism from it to `ZMod m`. A rational factorization whose factors
and inverses have such denominators reduces to a factorization over `ZMod m`
with the same pivots. For any finite collection of rational matrices there is
a prime beyond every denominator, so the reduction is available modulo every
power of that prime, and the shear programs of `Shear` then compute
`H ← H + A D` modulo `q^b` with exactly `rank A` interchanges. -/

namespace IntegerMultBounds.Swap.Modular

open Matrix Finset
open IntegerMultBounds.Swap.Shear (LowerTriangular pivotMatrix shearProgram run interchanges)
open IntegerMultBounds.Swap.LowerTriangular (Factorization factorization)
open IntegerMultBounds.Swap.PivotRank (length_eq_rank pivotMatrix_apply)

section Reduction
variable (m : ℕ)

/-- `num / den` evaluated in `ZMod m`; a ring homomorphism on the rationals whose
denominators are prime to `m`. -/
def ratMod (x : ℚ) : ZMod m := (x.num : ZMod m) * (x.den : ZMod m)⁻¹

theorem den_mul_inv {x : ℚ} (h : x.den.Coprime m) :
    (x.den : ZMod m) * (x.den : ZMod m)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one x.den h

theorem ratMod_mul_den {x : ℚ} (h : x.den.Coprime m) :
    ratMod m x * x.den = x.num := by
  unfold ratMod
  rw [mul_assoc, mul_comm ((x.den : ZMod m)⁻¹), den_mul_inv m h, mul_one]

theorem ratMod_unique {x : ℚ} (h : x.den.Coprime m) {z : ZMod m}
    (hz : z * x.den = x.num) : z = ratMod m x := by
  calc z = z * ((x.den : ZMod m) * (x.den : ZMod m)⁻¹) := by rw [den_mul_inv m h, mul_one]
    _ = ratMod m x := by rw [← mul_assoc, hz]; rfl

/-- Cancel a unit factor given by a coprime denominator product. -/
theorem cancel_coprime {u : ℕ} (hu : u.Coprime m) {a b : ZMod m} (h : a * u = b * u) : a = b := by
  have hu' : (u : ZMod m) * (u : ZMod m)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one u hu
  calc a = a * ((u : ZMod m) * (u : ZMod m)⁻¹) := by rw [hu', mul_one]
    _ = b * ((u : ZMod m) * (u : ZMod m)⁻¹) := by rw [← mul_assoc, h, mul_assoc]
    _ = b := by rw [hu', mul_one]

theorem ratMod_zero : ratMod m 0 = 0 := by
  simp [ratMod]

theorem ratMod_one : ratMod m 1 = 1 := by
  simp [ratMod]

/-- The integer identity behind addition of fractions. -/
theorem add_num_den (x y : ℚ) :
    (x.num * y.den + y.num * x.den) * ((x + y).den : ℤ) = (x + y).num * (x.den * y.den) := by
  have hx := Rat.mul_den_eq_num x
  have hy := Rat.mul_den_eq_num y
  have hxy := Rat.mul_den_eq_num (x + y)
  have : ((x.num * y.den + y.num * x.den) * ((x + y).den : ℤ) : ℚ) =
      ((x + y).num * (x.den * y.den) : ℤ) := by
    push_cast
    rw [← hx, ← hy, ← hxy]
    ring
  exact_mod_cast this

theorem mul_num_den (x y : ℚ) :
    (x.num * y.num) * ((x * y).den : ℤ) = (x * y).num * (x.den * y.den) := by
  have hx := Rat.mul_den_eq_num x
  have hy := Rat.mul_den_eq_num y
  have hxy := Rat.mul_den_eq_num (x * y)
  have : ((x.num * y.num) * ((x * y).den : ℤ) : ℚ) = ((x * y).num * (x.den * y.den) : ℤ) := by
    push_cast
    rw [← hx, ← hy, ← hxy]
    ring
  exact_mod_cast this

theorem ratMod_add {x y : ℚ} (hx : x.den.Coprime m) (hy : y.den.Coprime m) :
    ratMod m (x + y) = ratMod m x + ratMod m y := by
  have hxy : (x + y).den.Coprime m :=
    Nat.Coprime.coprime_dvd_left (Rat.add_den_dvd x y) (Nat.Coprime.mul_left hx hy)
  symm
  apply ratMod_unique m hxy
  apply cancel_coprime m (Nat.Coprime.mul_left hx hy)
  have h1 := ratMod_mul_den m hx
  have h2 := ratMod_mul_den m hy
  have key := congrArg (Int.cast : ℤ → ZMod m) (add_num_den x y)
  push_cast at key
  calc (ratMod m x + ratMod m y) * ((x + y).den : ZMod m) * ((x.den * y.den : ℕ) : ZMod m)
      = (ratMod m x * x.den * y.den + ratMod m y * y.den * x.den) * ((x + y).den : ZMod m) := by
        push_cast; ring
    _ = ((x.num : ZMod m) * y.den + (y.num : ZMod m) * x.den) * ((x + y).den : ZMod m) := by
        rw [h1, h2]
    _ = ((x + y).num : ZMod m) * ((x.den * y.den : ℕ) : ZMod m) := by
        push_cast; exact key

theorem ratMod_mul {x y : ℚ} (hx : x.den.Coprime m) (hy : y.den.Coprime m) :
    ratMod m (x * y) = ratMod m x * ratMod m y := by
  have hxy : (x * y).den.Coprime m :=
    Nat.Coprime.coprime_dvd_left (Rat.mul_den_dvd x y) (Nat.Coprime.mul_left hx hy)
  symm
  apply ratMod_unique m hxy
  apply cancel_coprime m (Nat.Coprime.mul_left hx hy)
  have h1 := ratMod_mul_den m hx
  have h2 := ratMod_mul_den m hy
  have key := congrArg (Int.cast : ℤ → ZMod m) (mul_num_den x y)
  push_cast at key
  calc ratMod m x * ratMod m y * ((x * y).den : ZMod m) * ((x.den * y.den : ℕ) : ZMod m)
      = (ratMod m x * x.den) * (ratMod m y * y.den) * ((x * y).den : ZMod m) := by
        push_cast; ring
    _ = (x.num : ZMod m) * (y.num : ZMod m) * ((x * y).den : ZMod m) := by rw [h1, h2]
    _ = ((x * y).num : ZMod m) * ((x.den * y.den : ℕ) : ZMod m) := by
        push_cast; exact key

/-- Rationals whose denominators are prime to `m`. -/
def denCoprime : Subring ℚ where
  carrier := {x | x.den.Coprime m}
  mul_mem' := fun {a b} ha hb =>
    Nat.Coprime.coprime_dvd_left (Rat.mul_den_dvd a b) (Nat.Coprime.mul_left ha hb)
  one_mem' := by
    show (1 : ℚ).den.Coprime m
    rw [Rat.den_one]
    exact Nat.coprime_one_left m
  add_mem' := fun {a b} ha hb =>
    Nat.Coprime.coprime_dvd_left (Rat.add_den_dvd a b) (Nat.Coprime.mul_left ha hb)
  zero_mem' := by
    show (0 : ℚ).den.Coprime m
    rw [Rat.den_zero]
    exact Nat.coprime_one_left m
  neg_mem' := fun {a} ha => by
    show (-a).den.Coprime m
    rw [Rat.neg_den]
    exact ha

theorem mem_denCoprime {x : ℚ} : x ∈ denCoprime m ↔ x.den.Coprime m := Iff.rfl

/-- The reduction homomorphism. -/
def toZMod : denCoprime m →+* ZMod m where
  toFun x := ratMod m x
  map_one' := ratMod_one m
  map_mul' x y := ratMod_mul m x.2 y.2
  map_zero' := ratMod_zero m
  map_add' x y := ratMod_add m x.2 y.2

end Reduction

section Matrices
variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν] (m : ℕ)

/-- Entrywise reduction modulo `m`. -/
def reduce (A : Matrix ι κ ℚ) : Matrix ι κ (ZMod m) := A.map (ratMod m)

/-- Every entry has denominator prime to `m`. -/
def Admissible (A : Matrix ι κ ℚ) : Prop := ∀ i j, (A i j).den.Coprime m

/-- The lift of an admissible matrix to the subring. -/
def lift (A : Matrix ι κ ℚ) (hA : Admissible m A) : Matrix ι κ (denCoprime m) :=
  of fun i j => ⟨A i j, hA i j⟩

omit [Fintype ι] [Fintype κ] in
theorem lift_map_val (A : Matrix ι κ ℚ) (hA : Admissible m A) :
    (lift m A hA).map (denCoprime m).subtype = A := by
  ext i j
  rfl

omit [Fintype ι] [Fintype κ] in
theorem reduce_lift (A : Matrix ι κ ℚ) (hA : Admissible m A) :
    reduce m A = (lift m A hA).map (toZMod m) := by
  ext i j
  rfl

omit [Fintype ι] [Fintype ν] in
theorem admissible_mul {A : Matrix ι κ ℚ} {B : Matrix κ ν ℚ} (hA : Admissible m A)
    (hB : Admissible m B) : Admissible m (A * B) := by
  intro i j
  have : A * B = (lift m A hA * lift m B hB).map (denCoprime m).subtype := by
    rw [Matrix.map_mul, lift_map_val, lift_map_val]
  rw [this, map_apply]
  exact ((lift m A hA * lift m B hB) i j).2

omit [Fintype ι] [Fintype ν] in
theorem reduce_mul {A : Matrix ι κ ℚ} {B : Matrix κ ν ℚ} (hA : Admissible m A)
    (hB : Admissible m B) : reduce m (A * B) = reduce m A * reduce m B := by
  have hAB : lift m (A * B) (admissible_mul m hA hB) = lift m A hA * lift m B hB := by
    apply Matrix.map_injective (denCoprime m).subtype_injective
    dsimp only
    rw [Matrix.map_mul, lift_map_val, lift_map_val, lift_map_val]
  rw [reduce_lift m A hA, reduce_lift m B hB, reduce_lift m (A * B) (admissible_mul m hA hB),
    hAB, Matrix.map_mul]

omit [Fintype ι] in
theorem reduce_one [DecidableEq ι] : reduce m (1 : Matrix ι ι ℚ) = 1 :=
  Matrix.map_one _ (ratMod_zero m) (ratMod_one m)

omit [Fintype ι] in
theorem admissible_one [DecidableEq ι] : Admissible m (1 : Matrix ι ι ℚ) := by
  intro i j
  by_cases h : i = j
  · subst h
    rw [one_apply_eq, Rat.den_one]
    exact Nat.coprime_one_left m
  · rw [one_apply_ne h, Rat.den_zero]
    exact Nat.coprime_one_left m

omit [Fintype ι] in
theorem reduce_lowerTriangular [LinearOrder ι] {E : Matrix ι ι ℚ} (hE : LowerTriangular E) :
    LowerTriangular (reduce m E) := by
  intro i j hij
  rw [reduce, map_apply, hE i j hij, ratMod_zero]

omit [Fintype ι] [Fintype κ] in
theorem reduce_pivotMatrix [DecidableEq ι] [DecidableEq κ] (L : List (ι × κ)) (hL : L.Nodup) :
    reduce m (pivotMatrix L) = (pivotMatrix L : Matrix ι κ (ZMod m)) := by
  ext i j
  rw [reduce, map_apply, pivotMatrix_apply (R := ℚ) L hL, pivotMatrix_apply (R := ZMod m) L hL]
  by_cases h : (i, j) ∈ L
  · rw [ite_eq_left h, ite_eq_left h, ratMod_one]
  · rw [ite_eq_right h, ite_eq_right h, ratMod_zero]

omit [Fintype ι] [Fintype κ] in
theorem admissible_pivotMatrix [DecidableEq ι] [DecidableEq κ] (L : List (ι × κ))
    (hL : L.Nodup) : Admissible m (pivotMatrix L : Matrix ι κ ℚ) := by
  intro i j
  rw [pivotMatrix_apply (R := ℚ) L hL]
  by_cases h : (i, j) ∈ L
  · rw [ite_eq_left h, Rat.den_one]
    exact Nat.coprime_one_left m
  · rw [ite_eq_right h, Rat.den_zero]
    exact Nat.coprime_one_left m

/-- Reducing the two factors of an inverse pair gives an inverse pair. -/
theorem reduce_inverse [DecidableEq ι] {E E' : Matrix ι ι ℚ} (hE : Admissible m E)
    (hE' : Admissible m E') (h : E * E' = 1) : reduce m E * reduce m E' = 1 := by
  rw [← reduce_mul m hE hE', h, reduce_one]

end Matrices

section Factorizations
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [LinearOrder ι] [LinearOrder κ] (m : ℕ)

/-- A rational factorization with admissible factors reduces to a factorization
over `ZMod m` with the same pivots. -/
theorem reduce_factorization {S : Finset ι} {T : Finset κ} {A : Matrix ι κ ℚ}
    (f : Factorization S T A) (h₁ : Admissible m f.E₁)
    (h₁' : Admissible m f.E₁') (h₂ : Admissible m f.E₂) (h₂' : Admissible m f.E₂') :
    LowerTriangular (reduce m f.E₁) ∧ LowerTriangular (reduce m f.E₁') ∧
      LowerTriangular (reduce m f.E₂) ∧ LowerTriangular (reduce m f.E₂') ∧
      reduce m f.E₁ * reduce m f.E₁' = 1 ∧ reduce m f.E₁' * reduce m f.E₁ = 1 ∧
      reduce m f.E₂ * reduce m f.E₂' = 1 ∧ reduce m f.E₂' * reduce m f.E₂ = 1 ∧
      reduce m A = reduce m f.E₁ * pivotMatrix f.L * reduce m f.E₂ := by
  have hL : f.L.Nodup := f.nodup₁.of_map _
  refine ⟨reduce_lowerTriangular m f.lower₁, reduce_lowerTriangular m f.lower₁',
    reduce_lowerTriangular m f.lower₂, reduce_lowerTriangular m f.lower₂',
    reduce_inverse m h₁ h₁' f.inv₁, reduce_inverse m h₁' h₁ f.inv₁',
    reduce_inverse m h₂ h₂' f.inv₂, reduce_inverse m h₂' h₂ f.inv₂', ?_⟩
  have hP := admissible_pivotMatrix m (ι := ι) (κ := κ) f.L hL
  have h := congrArg (reduce m) f.eq
  rw [reduce_mul m (admissible_mul m h₁ hP) h₂, reduce_mul m h₁ hP,
    reduce_pivotMatrix m f.L hL] at h
  exact h

/-- The denominators appearing in a matrix. -/
def denominators (A : Matrix ι κ ℚ) : Finset ℕ := univ.image fun p : ι × κ => (A p.1 p.2).den

omit [LinearOrder ι] [LinearOrder κ] in
theorem admissible_of_lt {A : Matrix ι κ ℚ} {q : ℕ} (hq : q.Prime)
    (h : ∀ d ∈ denominators A, d < q) (b : ℕ) : Admissible (q ^ b) A := by
  intro i j
  have hd : (A i j).den ∈ denominators A := mem_image.mpr ⟨(i, j), mem_univ _, rfl⟩
  have hlt := h _ hd
  have hpos := (A i j).den_pos
  have : q.Coprime (A i j).den := by
    rw [hq.coprime_iff_not_dvd]
    intro hdvd
    exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr hlt)
  exact Nat.Coprime.pow_right b this.symm

/-- The denominators of a factorization, its inverses, and its matrix. -/
def factorizationDenominators {S : Finset ι} {T : Finset κ} {A : Matrix ι κ ℚ}
    (f : Factorization S T A) : Finset ℕ :=
  denominators A ∪ denominators f.E₁ ∪ denominators f.E₁' ∪ denominators f.E₂ ∪ denominators f.E₂'

/-- Lemma 4.1 modulo every power of a prime beyond the denominators: a rational
matrix factors over `ZMod (q ^ b)` with exactly `rank A` pivots. -/
theorem reduce_factorization_of_prime {A : Matrix ι κ ℚ} (f : Factorization univ univ A)
    {q : ℕ} (hq : q.Prime) (hd : ∀ d ∈ factorizationDenominators f, d < q) (b : ℕ) :
    f.L.length = A.rank ∧
      LowerTriangular (reduce (q ^ b) f.E₁) ∧ LowerTriangular (reduce (q ^ b) f.E₁') ∧
      LowerTriangular (reduce (q ^ b) f.E₂) ∧ LowerTriangular (reduce (q ^ b) f.E₂') ∧
      reduce (q ^ b) f.E₁ * reduce (q ^ b) f.E₁' = 1 ∧
      reduce (q ^ b) f.E₁' * reduce (q ^ b) f.E₁ = 1 ∧
      reduce (q ^ b) f.E₂ * reduce (q ^ b) f.E₂' = 1 ∧
      reduce (q ^ b) f.E₂' * reduce (q ^ b) f.E₂ = 1 ∧
      reduce (q ^ b) A = reduce (q ^ b) f.E₁ * pivotMatrix f.L * reduce (q ^ b) f.E₂ := by
  have hsub : ∀ D ∈ [denominators A, denominators f.E₁, denominators f.E₁', denominators f.E₂,
      denominators f.E₂'], ∀ d ∈ D, d < q := by
    intro D hD d hdD
    apply hd
    unfold factorizationDenominators
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD with rfl | rfl | rfl | rfl | rfl
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_left _ hdD)))
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_right _ hdD)))
    · exact mem_union_left _ (mem_union_left _ (mem_union_right _ hdD))
    · exact mem_union_left _ (mem_union_right _ hdD)
    · exact mem_union_right _ hdD
  refine ⟨length_eq_rank f, ?_⟩
  exact reduce_factorization (q ^ b) f
    (admissible_of_lt hq (hsub _ (by simp)) b)
    (admissible_of_lt hq (hsub _ (by simp)) b)
    (admissible_of_lt hq (hsub _ (by simp)) b)
    (admissible_of_lt hq (hsub _ (by simp)) b)

/-- A prime beyond a finite set of denominators. -/
theorem exists_prime_gt (D : Finset ℕ) : ∃ q : ℕ, q.Prime ∧ 2 < q ∧ ∀ d ∈ D, d < q := by
  obtain ⟨q, hq, hprime⟩ := Nat.exists_infinite_primes (D.sup id + 3)
  refine ⟨q, hprime, by omega, ?_⟩
  intro d hd
  have := Finset.le_sup (f := id) hd
  simp only [id] at this
  omega

end Factorizations

section Shear
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Lemma 4.2: for a finite collection of rational matrices there is an odd prime
`q` such that, modulo every `q^b`, each matrix `A` of the collection has a shear
program computing `H ← H + A D` with exactly `rank A` interchanges, whose other
operations are lower triangular transformations and later-field updates. -/
theorem exists_prime_shear (𝒜 : Finset (Matrix ι ι ℚ)) :
    ∃ q : ℕ, q.Prime ∧ 2 < q ∧ ∀ A ∈ 𝒜, ∀ b : ℕ,
      ∃ (E₁ E₁' E₂ E₂' : Matrix ι ι (ZMod (q ^ b))) (L : List (ι × ι)),
        LowerTriangular E₁ ∧ LowerTriangular E₁' ∧ LowerTriangular E₂ ∧ LowerTriangular E₂' ∧
        interchanges (shearProgram E₁ E₁' E₂ E₂' L) = A.rank ∧
        ∀ s, run (shearProgram E₁ E₁' E₂ E₂' L) s = (s.1 + reduce (q ^ b) A *ᵥ s.2, s.2) := by
  classical
  let f : ∀ A : Matrix ι ι ℚ, Factorization univ univ A := fun A => Classical.choice (factorization A)
  obtain ⟨q, hq, h2, hd⟩ := exists_prime_gt (𝒜.biUnion fun A => factorizationDenominators (f A))
  refine ⟨q, hq, h2, ?_⟩
  intro A hA b
  have hdA : ∀ d ∈ factorizationDenominators (f A), d < q := fun d hdd =>
    hd d (mem_biUnion.mpr ⟨A, hA, hdd⟩)
  obtain ⟨hlen, hl₁, hl₁', hl₂, hl₂', hi₁, hi₁', hi₂, hi₂', heq⟩ :=
    reduce_factorization_of_prime (f A) hq hdA b
  refine ⟨reduce (q ^ b) (f A).E₁, reduce (q ^ b) (f A).E₁', reduce (q ^ b) (f A).E₂,
    reduce (q ^ b) (f A).E₂', (f A).L, hl₁, hl₁', hl₂, hl₂', ?_, ?_⟩
  · rw [Shear.shearProgram_interchanges, hlen]
  · intro s
    rw [Shear.shearProgram_run _ _ _ _ hi₁ hi₂', heq]

end Shear

end IntegerMultBounds.Swap.Modular
