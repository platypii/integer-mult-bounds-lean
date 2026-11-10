module

public import IntegerMultBounds.MathlibTM2.M8.ReversedExchange
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith

/-!
# Cover labels and weighted reversed children

A class-indexed cover stores the stream of a role at every label `g`, an invertible matrix over
the atom ring, in the frames `g U g⁻¹`. This file has the algebra that the cover node needs on top
of `M8.ReversedExchange`. All of it holds over every commutative ring.

* `exchange_conj`, `revExchangeOf_conj`: conjugating by a label turns the partial swap of `P` into
  the partial swap of `g P g⁻¹`. In the reversed frame the label acts as `diag(g, C g C)`, so the
  full reversed interchange is the same at every label (`revExchangeOf_one_conj`).
* `label_route`: a route `σ` changes the label from `g` to `g σ` and the local projector from `M`
  to `σ⁻¹ M σ`, and leaves the frame `g M g⁻¹` unchanged. A route therefore moves label
  coordinates and no payload coordinate.
* `weighted`: the weighted reversed interchange `F_A (h, d) = (A C d, C A⁻¹ h)`. It is the
  conjugate of the reversed interchange by `diag(A, 1)` (`weighted_eq`) and an involution
  (`weighted_weighted`).
* `weighted_factor`: the conjugate by `diag(A, 1)` of a reversed exchange with `P C = L Π R` is
  the conjugated adapters `A L A⁻¹`, `A L⁻¹ A⁻¹`, the shears by `K A⁻¹`, and the conjugated
  interchanges.
* `diag_swaps`, `weighted_child`: for diagonal weights the conjugated interchanges exchange
  `h_i` with `d_j` up to the unit `δ_i` on every pivot. On the reversed pivots this is one
  weighted reversed child on the first `r` head coordinates and the last `r` tail coordinates.
* `lower_diag_conj`: conjugating a lower-triangular adapter by diagonal weights keeps it lower
  triangular.
* `weighted_good`, `weighted_good_child`: if `P C = L Δ Π R` with unit pivots `Δ`, the pivots
  join the incoming weights, and one good move is one weighted child with weights `α δ`.
* `leaf_word`: a weighted exchange of two atoms is four ordinary exchanges, three shears and one
  sign.
* `fallback_children`: the elimination fallback on `2m` coordinates uses fewer than `32 m²`
  children.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.Weighted

open Matrix
open IntegerMultBounds.Swap.Shear (State Op run pivotMatrix LowerTriangular)
open IntegerMultBounds.Swap.PivotRank (pivotMatrix_apply)
open IntegerMultBounds.MathlibTM2.M8.Exchange
  (exchange transform cross swaps kMat indicator swaps_run pivot_row_zero pivot_col_zero)
open IntegerMultBounds.MathlibTM2.M8.ReversedExchange
  (revExchangeOf revExchangeOf_factor transform_comp revPivots revPivots_fst revPivots_snd
    mem_revPivots)

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-! ### Labels -/

/-- Conjugation by a label: the partial swap of `P` becomes the partial swap of `g P g⁻¹`. -/
theorem exchange_conj (g g' P : Matrix ι ι R) (hg : g * g' = 1) (s : State ι R) :
    transform g g (exchange P (transform g' g' s)) = exchange (g * P * g') s := by
  have h1 : g * ((1 - P) * g') = 1 - g * (P * g') := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, hg]
  simp only [transform, exchange, mulVec_add, mulVec_mulVec, h1, Matrix.mul_assoc]

/-- In the reversed frame a label acts as `diag(g, C g C)`. -/
theorem revExchangeOf_conj (C : Matrix ι ι R) (hC : C * C = 1) (g g' P : Matrix ι ι R)
    (hg : g * g' = 1) (s : State ι R) :
    transform g (C * g * C) (revExchangeOf C P (transform g' (C * g' * C) s)) =
      revExchangeOf C (g * P * g') s := by
  have hCC (A : Matrix ι ι R) : C * (C * A) = A := by rw [← Matrix.mul_assoc, hC, Matrix.one_mul]
  rw [revExchangeOf, revExchangeOf, ← exchange_conj g g' P hg]
  simp only [transform_comp, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, hC, hCC]

/-- The full reversed interchange is the same at every label. -/
theorem revExchangeOf_one_conj (C : Matrix ι ι R) (hC : C * C = 1) (g g' : Matrix ι ι R)
    (hg : g * g' = 1) (s : State ι R) :
    transform g (C * g * C) (revExchangeOf C 1 (transform g' (C * g' * C) s)) =
      revExchangeOf C 1 s := by
  rw [revExchangeOf_conj C hC g g' 1 hg, Matrix.mul_one, hg]

/-- A route changes the label and the local projector together and keeps the frame. -/
theorem label_route (g g' σ σ' M : Matrix ι ι R) (hσ : σ * σ' = 1) :
    g * σ * (σ' * M * σ) * (σ' * g') = g * M * g' := by
  have hs (A : Matrix ι ι R) : σ * (σ' * A) = A := by rw [← Matrix.mul_assoc, hσ, Matrix.one_mul]
  simp only [Matrix.mul_assoc, hs]

/-! ### The weighted reversed interchange -/

/-- The weighted reversed interchange `F_A (h, d) = (A C d, C A⁻¹ h)`. -/
def weighted (C A A' : Matrix ι ι R) (s : State ι R) : State ι R :=
  (A *ᵥ (C *ᵥ s.2), C *ᵥ (A' *ᵥ s.1))

/-- `F_A` is the reversed interchange conjugated by `diag(A, 1)`. -/
theorem weighted_eq (C A A' : Matrix ι ι R) (s : State ι R) :
    transform A 1 (revExchangeOf C 1 (transform A' 1 s)) = weighted C A A' s := by
  simp [weighted, revExchangeOf, transform, exchange]

theorem weighted_weighted (C A A' : Matrix ι ι R) (hC : C * C = 1) (hA : A * A' = 1)
    (hA' : A' * A = 1) (s : State ι R) : weighted C A A' (weighted C A A' s) = s := by
  have hCC (B : Matrix ι ι R) : C * (C * B) = B := by rw [← Matrix.mul_assoc, hC, Matrix.one_mul]
  have hAA (B : Matrix ι ι R) : A' * (A * B) = B := by rw [← Matrix.mul_assoc, hA', Matrix.one_mul]
  simp only [weighted, mulVec_mulVec, hCC, hAA, hA, hC, one_mulVec]

theorem cross_transform (K A : Matrix ι ι R) (s : State ι R) :
    cross K (transform A 1 s) = transform A 1 (cross (K * A) s) := by
  simp only [cross, transform, one_mulVec, mulVec_mulVec]

/-- **The weighted reversed exchange program.** Conjugating the reversed exchange of `P` by
`diag(A, 1)` conjugates the head adapters and multiplies the shear by `A⁻¹`. The interchanges
are conjugated by `diag(A, 1)`; `diag_swaps` evaluates them for diagonal `A`. -/
theorem weighted_factor (C : Matrix ι ι R) (hC : C * C = 1) (A A' : Matrix ι ι R)
    (hA' : A' * A = 1) (L L' R' R'' : Matrix ι ι R) (pivots : List (ι × ι))
    (h₁ : (pivots.map Prod.fst).Nodup) (h₂ : (pivots.map Prod.snd).Nodup)
    (hL : L * L' = 1) (hL' : L' * L = 1) (hR : R' * R'' = 1) (hR' : R'' * R' = 1)
    (P : Matrix ι ι R) (hP : P * C = L * pivotMatrix pivots * R') (hidem : P * P = P)
    (s : State ι R) :
    transform (A * L * A') R'' (cross (-(kMat (pivotMatrix pivots) (R' * C * L) * A'))
      (transform A 1 (run (swaps pivots) (transform A' 1
        (cross (kMat (pivotMatrix pivots) (R' * C * L) * A')
          (transform (A * L' * A') R' s)))))) =
      transform A 1 (revExchangeOf C P (transform A' 1 s)) := by
  have hAA (B : Matrix ι ι R) : A' * (A * B) = B := by rw [← Matrix.mul_assoc, hA', Matrix.one_mul]
  have hneg (K : Matrix ι ι R) : -(K * A') * A = -K := by
    rw [Matrix.neg_mul, Matrix.mul_assoc, hA', Matrix.mul_one]
  rw [← revExchangeOf_factor C hC L L' R' R'' pivots h₁ h₂ hL hL' hR hR' P hP hidem,
    ← cross_transform, cross_transform (-(kMat (pivotMatrix pivots) (R' * C * L) * A')) A, hneg]
  simp only [transform_comp, Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one, hAA, hA']

/-- Interchanges conjugated by diagonal weights: on a pivot `(i, j)`, `h_i ← δ_i d_j` and
`d_j ← δ_i⁻¹ h_i`; every other coordinate is unchanged. -/
theorem diag_swaps (L : List (ι × ι)) (h₁ : (L.map Prod.fst).Nodup)
    (h₂ : (L.map Prod.snd).Nodup) (δ δ' : ι → R) (hδ : ∀ i, δ i * δ' i = 1) (s : State ι R) :
    transform (diagonal δ) 1 (run (swaps L) (transform (diagonal δ') 1 s)) =
      (fun i => if i ∈ L.map Prod.fst then δ i * (pivotMatrix L *ᵥ s.2) i else s.1 i,
        fun j => if j ∈ L.map Prod.snd then ((pivotMatrix L)ᵀ *ᵥ fun i => δ' i * s.1 i) j
          else s.2 j) := by
  have hL : L.Nodup := h₁.of_map _
  have hd : diagonal δ' *ᵥ s.1 = fun i => δ' i * s.1 i := funext fun i => mulVec_diagonal _ _ _
  rw [swaps_run L h₁ h₂]
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · simp only [transform, indicator, mulVec_diagonal, Pi.add_apply, Pi.sub_apply, one_mulVec]
    by_cases hi : i ∈ L.map Prod.fst
    · rw [ite_eq_left hi, ite_eq_left hi]
      ring
    · rw [ite_eq_right hi, ite_eq_right hi]
      have h0 : (pivotMatrix L *ᵥ s.2) i = 0 :=
        Finset.sum_eq_zero fun j _ => by
          show pivotMatrix L i j * s.2 j = 0
          rw [pivot_row_zero L hi hL, zero_mul]
      rw [h0]
      linear_combination s.1 i * hδ i
  · simp only [transform, indicator, mulVec_diagonal, Pi.add_apply, Pi.sub_apply, one_mulVec, hd]
    by_cases hj : j ∈ L.map Prod.snd
    · rw [ite_eq_left hj, ite_eq_left hj]
      ring
    · rw [ite_eq_right hj, ite_eq_right hj]
      have h0 : ((pivotMatrix L)ᵀ *ᵥ fun i => δ' i * s.1 i) j = 0 :=
        Finset.sum_eq_zero fun i _ => by
          show pivotMatrix L i j * (δ' i * s.1 i) = 0
          rw [pivot_col_zero L hj hL, zero_mul]
      rw [h0]
      ring

/-- The weighted reversed interchange of the first `r` head coordinates with the last `r` tail
coordinates: `h_k ← ω_k d_{m-1-k}` and `d_{m-1-k} ← ω_k⁻¹ h_k` for `k < r`. -/
def child {m : ℕ} (r : ℕ) (ω ω' : Fin m → R) (s : State (Fin m) R) : State (Fin m) R :=
  (fun i => if i.val < r then ω i * s.2 i.rev else s.1 i,
    fun j => if j.rev.val < r then ω' j.rev * s.1 j.rev else s.2 j)

/-- **One weighted reversed child.** On the reversed pivots the conjugated interchanges are
`h_k ← δ_k d_{m-1-k}` and `d_{m-1-k} ← δ_k⁻¹ h_k` for `k < r`: the weighted reversed interchange
of the first `r` head coordinates with the last `r` tail coordinates, with weights `δ`. -/
theorem weighted_child {m : ℕ} (r : ℕ) (δ δ' : Fin m → R) (hδ : ∀ i, δ i * δ' i = 1)
    (s : State (Fin m) R) :
    transform (diagonal δ) 1 (run (swaps (revPivots m r)) (transform (diagonal δ') 1 s)) =
      child r δ δ' s := by
  rw [child]
  have hL : (revPivots m r).Nodup := (revPivots_fst m r).of_map _
  have hfst (i : Fin m) : i ∈ (revPivots m r).map Prod.fst ↔ i.val < r := by
    rw [List.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ((mem_revPivots m r p.1 p.2).mp hp).1
    · intro hi
      exact ⟨(i, i.rev), (mem_revPivots m r i i.rev).mpr ⟨hi, rfl⟩, rfl⟩
  have hsnd (j : Fin m) : j ∈ (revPivots m r).map Prod.snd ↔ j.rev.val < r := by
    rw [List.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨hlt, heq⟩ := (mem_revPivots m r p.1 p.2).mp hp
      rw [heq, Fin.rev_rev]
      exact hlt
    · intro hj
      exact ⟨(j.rev, j), (mem_revPivots m r j.rev j).mpr ⟨hj, (Fin.rev_rev j).symm⟩, rfl⟩
  rw [diag_swaps _ (revPivots_fst m r) (revPivots_snd m r) δ δ' hδ]
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · simp only [hfst]
    by_cases hi : i.val < r
    · rw [ite_eq_left hi, ite_eq_left hi]
      congr 1
      rw [mulVec, dotProduct, Finset.sum_eq_single i.rev]
      · rw [pivotMatrix_apply _ hL, ite_eq_left ((mem_revPivots m r i i.rev).mpr ⟨hi, rfl⟩), one_mul]
      · intro k _ hk
        rw [pivotMatrix_apply _ hL, ite_eq_right, zero_mul]
        intro hmem
        exact hk ((mem_revPivots m r i k).mp hmem).2
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [ite_eq_right hi, ite_eq_right hi]
  · simp only [hsnd]
    by_cases hj : j.rev.val < r
    · rw [ite_eq_left hj, ite_eq_left hj, mulVec, dotProduct, Finset.sum_eq_single j.rev]
      · rw [transpose_apply, pivotMatrix_apply _ hL,
          ite_eq_left ((mem_revPivots m r j.rev j).mpr ⟨hj, (Fin.rev_rev j).symm⟩), one_mul]
      · intro k _ hk
        rw [transpose_apply, pivotMatrix_apply _ hL, ite_eq_right, zero_mul]
        intro hmem
        apply hk
        rw [((mem_revPivots m r k j).mp hmem).2, Fin.rev_rev]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [ite_eq_right hj, ite_eq_right hj]

/-- Diagonal weights keep an adapter lower triangular. -/
theorem lower_diag_conj {m : ℕ} {L : Matrix (Fin m) (Fin m) R} (hL : LowerTriangular L)
    (δ δ' : Fin m → R) : LowerTriangular (diagonal δ * L * diagonal δ') := by
  intro i j hij
  rw [mul_diagonal, diagonal_mul, hL i j hij, mul_zero, zero_mul]

/-! ### Pivots become child weights -/

theorem diagonal_inv_mul (δ δ' : ι → R) (hδ : ∀ i, δ i * δ' i = 1) :
    diagonal δ * diagonal δ' = (1 : Matrix ι ι R) := by
  rw [diagonal_mul_diagonal]
  simp only [hδ]
  exact diagonal_one

theorem diagonal_comm (δ ε : ι → R) : diagonal δ * diagonal ε = diagonal ε * diagonal δ := by
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem transform_left (D X Y : Matrix ι ι R) (s : State ι R) :
    transform (D * X) Y s = transform D 1 (transform X Y s) := by
  rw [transform_comp, Matrix.one_mul]

theorem transform_right (X D Y : Matrix ι ι R) (s : State ι R) :
    transform (X * D) Y s = transform X Y (transform D 1 s) := by
  rw [transform_comp, Matrix.mul_one]

theorem transform_diag (A B : Matrix ι ι R) (s : State ι R) :
    transform A 1 (transform B 1 s) = transform (A * B) 1 s := by
  rw [transform_comp, Matrix.one_mul]

theorem transform_cross_neg (D D' : Matrix ι ι R) (hD : D' * D = 1) (M : Matrix ι ι R)
    (s : State ι R) :
    transform D 1 (cross (-M) s) = cross (-(M * D')) (transform D 1 s) := by
  rw [cross_transform, Matrix.neg_mul, Matrix.mul_assoc, hD, Matrix.mul_one]

/-- Moving the pivots `δ` from the adapters to the weights of the interchanges. -/
theorem pivots_to_weights (α α' δ δ' : ι → R) (hδ : ∀ i, δ i * δ' i = 1)
    (K X X' Y Y' : Matrix ι ι R) (f : State ι R → State ι R) (s : State ι R) :
    transform (diagonal α * X * diagonal α') Y
      (cross (-(K * diagonal fun i => α' i * δ' i))
        (transform (diagonal fun i => α i * δ i) 1 (f (transform (diagonal fun i => α' i * δ' i) 1
          (cross (K * diagonal fun i => α' i * δ' i)
            (transform (diagonal α * X' * diagonal α') Y' s)))))) =
      transform (diagonal α * (X * diagonal δ) * diagonal α') Y
        (cross (-(K * diagonal α'))
          (transform (diagonal α) 1 (f (transform (diagonal α') 1
            (cross (K * diagonal α')
              (transform (diagonal α * (diagonal δ' * X') * diagonal α') Y' s)))))) := by
  have hαδ : (diagonal fun i => α i * δ i) = diagonal δ * diagonal α := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hα'δ' : (diagonal fun i => α' i * δ' i) = diagonal α' * diagonal δ' :=
    (diagonal_mul_diagonal _ _).symm
  have hδ'δ : diagonal δ' * diagonal δ = (1 : Matrix ι ι R) :=
    diagonal_inv_mul δ' δ fun i => by rw [mul_comm]; exact hδ i
  have eA : diagonal α * (diagonal δ' * X') * diagonal α' =
      diagonal δ' * (diagonal α * X' * diagonal α') := by
    rw [← Matrix.mul_assoc (diagonal α), diagonal_comm α δ']
    simp only [Matrix.mul_assoc]
  have eB : diagonal α * (X * diagonal δ) * diagonal α' =
      diagonal α * X * diagonal α' * diagonal δ := by
    simp only [Matrix.mul_assoc]
    rw [diagonal_comm δ α']
  rw [hαδ, hα'δ', eA, eB,
    transform_left (diagonal δ') (diagonal α * X' * diagonal α') Y' s,
    cross_transform (K * diagonal α') (diagonal δ'),
    transform_diag (diagonal α') (diagonal δ'),
    transform_right (diagonal α * X * diagonal α') (diagonal δ) Y,
    transform_cross_neg (diagonal δ) (diagonal δ') hδ'δ (K * diagonal α'),
    transform_diag (diagonal δ) (diagonal α), Matrix.mul_assoc K]

/-- **The good normal form with weights.** Let `P C = L Δ Π R` with invertible adapters `L`, `R`
and unit pivots `Δ = diag(δ)`. Under incoming weights `α`, the reversed exchange of `P` is the
adapters `α L α⁻¹` and `R`, the shears, and the interchanges with weights `α δ`. The pivots are
never applied as scalings: they are the weights of the child. -/
theorem weighted_good (C : Matrix ι ι R) (hC : C * C = 1) (α α' δ δ' : ι → R)
    (hα : ∀ i, α i * α' i = 1) (hδ : ∀ i, δ i * δ' i = 1)
    (L L' R' R'' : Matrix ι ι R) (pivots : List (ι × ι))
    (h₁ : (pivots.map Prod.fst).Nodup) (h₂ : (pivots.map Prod.snd).Nodup)
    (hL : L * L' = 1) (hL' : L' * L = 1) (hR : R' * R'' = 1) (hR' : R'' * R' = 1)
    (P : Matrix ι ι R) (hP : P * C = L * diagonal δ * pivotMatrix pivots * R')
    (hidem : P * P = P) (s : State ι R) :
    transform (diagonal α * L * diagonal α') R''
      (cross (-(kMat (pivotMatrix pivots) (R' * C * (L * diagonal δ)) *
          diagonal fun i => α' i * δ' i))
        (transform (diagonal fun i => α i * δ i) 1 (run (swaps pivots)
          (transform (diagonal fun i => α' i * δ' i) 1
            (cross (kMat (pivotMatrix pivots) (R' * C * (L * diagonal δ)) *
                diagonal fun i => α' i * δ' i)
              (transform (diagonal α * L' * diagonal α') R' s)))))) =
      transform (diagonal α) 1 (revExchangeOf C P (transform (diagonal α') 1 s)) := by
  have hδδ' := diagonal_inv_mul δ δ' hδ
  have hδ'δ : diagonal δ' * diagonal δ = (1 : Matrix ι ι R) :=
    diagonal_inv_mul δ' δ fun i => by rw [mul_comm]; exact hδ i
  have hα'α : diagonal α' * diagonal α = (1 : Matrix ι ι R) :=
    diagonal_inv_mul α' α fun i => by rw [mul_comm]; exact hα i
  have hLδ : L * diagonal δ * (diagonal δ' * L') = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal δ), hδδ', Matrix.one_mul, hL]
  have hLδ' : diagonal δ' * L' * (L * diagonal δ) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc L', hL', Matrix.one_mul, hδ'δ]
  exact (pivots_to_weights α α' δ δ' hδ _ L L' R'' R' (run (swaps pivots)) s).trans
    (weighted_factor C hC (diagonal α) (diagonal α') hα'α (L * diagonal δ) (diagonal δ' * L')
      R' R'' pivots h₁ h₂ hLδ hLδ' hR hR' P hP hidem s)

/-- **One weighted child per good move.** With the reversed pivots, the reversed exchange of `P`
under weights `α` is the conjugated adapters and shears around one weighted reversed child with
weights `α δ`. -/
theorem weighted_good_child {m : ℕ} (r : ℕ) (α α' δ δ' : Fin m → R)
    (hα : ∀ i, α i * α' i = 1) (hδ : ∀ i, δ i * δ' i = 1)
    (L L' R' R'' : Matrix (Fin m) (Fin m) R)
    (hL : L * L' = 1) (hL' : L' * L = 1) (hR : R' * R'' = 1) (hR' : R'' * R' = 1)
    (P : Matrix (Fin m) (Fin m) R)
    (hP : P * M8.ReversedExchange.rev m = L * diagonal δ * pivotMatrix (revPivots m r) * R')
    (hidem : P * P = P) (s : State (Fin m) R) :
    transform (diagonal α * L * diagonal α') R''
      (cross (-(kMat (pivotMatrix (revPivots m r))
            (R' * M8.ReversedExchange.rev m * (L * diagonal δ)) *
          diagonal fun i => α' i * δ' i))
        (child r (fun i => α i * δ i) (fun i => α' i * δ' i)
          (cross (kMat (pivotMatrix (revPivots m r))
              (R' * M8.ReversedExchange.rev m * (L * diagonal δ)) *
              diagonal fun i => α' i * δ' i)
            (transform (diagonal α * L' * diagonal α') R' s)))) =
      transform (diagonal α) 1
        (revExchangeOf (M8.ReversedExchange.rev m) P (transform (diagonal α') 1 s)) := by
  have hαδ (i : Fin m) : α i * δ i * (α' i * δ' i) = 1 := by
    rw [mul_mul_mul_comm, hα, hδ, mul_one]
  rw [← weighted_good (M8.ReversedExchange.rev m) M8.ReversedExchange.rev_mul_rev α α' δ δ' hα hδ
    L L' R' R'' (revPivots m r) (revPivots_fst m r) (revPivots_snd m r) hL hL' hR hR' P hP hidem,
    weighted_child r (fun i => α i * δ i) (fun i => α' i * δ' i) hαδ]

/-! ### The stopped leaf and the fallback count -/

/-- The shear `d ← d + c h` of two atoms. -/
def shear (c : R) (p : R × R) : R × R := (p.1, p.2 + c * p.1)

/-- **The weighted leaf.** Four exchanges, three shears and one sign give `(h, d) ↦ (a d, a⁻¹ h)`.
Every shear adds a multiple of the earlier atom to the later one. -/
theorem leaf_word (a a' : R) (h : a * a' = 1) (p : R × R) :
    (fun q : R × R => (q.1, -q.2))
      ((shear a ((shear (-a') ((shear a p.swap).swap)).swap)).swap) = (a * p.2, a' * p.1) := by
  obtain ⟨x, y⟩ := p
  refine Prod.ext ?_ ?_
  · dsimp only [shear, Prod.swap]
    linear_combination (-(x + a * y)) * h
  · dsimp only [shear, Prod.swap]
    linear_combination y * h

/-- Unit-pivot elimination of an invertible matrix on `2m` coordinates uses at most
`2m (2m - 1)` additions, `2m` exchanges and `2m - 1` diagonal pairs. With six children per addition
and per diagonal pair and three per exchange, a fallback has fewer than `32 m²` children. -/
theorem fallback_children (m : ℕ) (hm : 1 ≤ m) :
    6 * ((2 * m) * (2 * m - 1)) + 3 * (2 * m) + 6 * (2 * m - 1) < 32 * m ^ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have h2 : 6 * ((2 * (k + 1)) * (2 * k + 1)) + 3 * (2 * (k + 1)) + 6 * (2 * k + 1) =
      24 * k ^ 2 + 54 * k + 24 := by ring
  have h3 : 32 * (k + 1) ^ 2 = 32 * k ^ 2 + 64 * k + 32 := by ring
  rw [h1, h2, h3]
  linarith [Nat.zero_le (k ^ 2), Nat.zero_le k]

end IntegerMultBounds.MathlibTM2.Cover.Weighted
