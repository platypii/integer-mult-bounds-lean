module

public import IntegerMultBounds.MathlibTM2.M8.AtomOps
public import IntegerMultBounds.Swap.Modular
public import Mathlib.GroupTheory.Perm.Support

/-!
# Label routes as atom programs

A route sends the label `g` to `g σ`. The label box is all of `M_m(R)`, laid out as `m`
coordinates, one per column of `g`, each carrying `m` atoms (`cols`). Right multiplication mixes
whole columns with scalar coefficients, so a route is an atom program on `m` coordinates:

* `lower_route`: `g ↦ g Eᵀ` for lower-triangular `E` is the ordered program of `E` run atomwise.
  Its operations are legal atom operations (`atomOp_legal`).
* `pivot_route`: `g ↦ g Πᵀ` for a full pivot matrix moves whole columns by a permutation
  (`exists_perm`), which is a product of at most `m - 1` exchanges of two columns
  (`exists_swaps`).
* `route`: with `σᵀ = E₁ Π E₂`, the route is the program of `E₂`, the column permutation, and the
  program of `E₁`.
* `exists_route`: an invertible rational `σ` has such a route over `ZMod (q ^ b)` for every prime
  `q` beyond finitely many denominators and every `b`.

So a route costs two ordered passes and at most `m - 1` leaf interchanges of two columns, with no
carries and no class tapes.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.Route

open Matrix
open IntegerMultBounds.Networks
open IntegerMultBounds.Swap.Shear (LowerTriangular pivotMatrix)
open IntegerMultBounds.Swap.PivotRank (pivotMatrix_apply length_eq_rank)
open IntegerMultBounds.Swap.Modular (reduce factorizationDenominators reduce_factorization_of_prime)
open IntegerMultBounds.MathlibTM2.M8.AtomOps (AtomOp atomExecute AtomLegal Distinct)

variable {n f m : ℕ} {R : Type*} [CommRing R]

/-! ### Ordinary operations run atomwise -/

/-- An ordinary operation on coordinates as the same operation on every atom. -/
def atomOp : OrderedAffine.Op (Fin n) R → AtomOp n R
  | .scale t c => .scale t c
  | .shift t k c => .shift t k c

/-- The run of a list of atom operations. -/
def atomRun (ops : List (AtomOp n R)) (x : Fin n → Fin f → R) : Fin n → Fin f → R :=
  ops.foldl (fun x op => atomExecute op x) x

theorem atomExecute_level (op : OrderedAffine.Op (Fin n) R) (x : Fin n → Fin f → R) (l : Fin f) :
    (fun t => atomExecute (atomOp op) x t l) = OrderedAffine.execute op (fun t => x t l) := by
  cases op with
  | scale t c =>
    funext k
    by_cases h : k = t
    · subst h; simp [atomOp, atomExecute, OrderedAffine.execute]
    · simp [atomOp, atomExecute, OrderedAffine.execute, Function.update_of_ne h]
  | shift t j c =>
    funext k
    by_cases h : k = t
    · subst h; simp [atomOp, atomExecute, OrderedAffine.execute]
    · simp [atomOp, atomExecute, OrderedAffine.execute, Function.update_of_ne h]

/-- Each atom level of an atomwise run is the ordinary run on that level. -/
theorem atomRun_level (ops : List (OrderedAffine.Op (Fin n) R)) (x : Fin n → Fin f → R)
    (l : Fin f) :
    (fun t => atomRun (ops.map atomOp) x t l) = OrderedAffine.run ops (fun t => x t l) := by
  induction ops generalizing x with
  | nil => rfl
  | cons op ops ih =>
    change (fun t => atomRun (ops.map atomOp) (atomExecute (atomOp op) x) t l) =
      OrderedAffine.run ops (OrderedAffine.execute op fun t => x t l)
    rw [ih, atomExecute_level]

theorem atomOp_legal {op : OrderedAffine.Op (Fin n) R} (h : OrderedAffine.Legal op) :
    AtomLegal (atomOp op) ∧ Distinct (atomOp op) := by
  cases op with
  | scale t c => exact ⟨h, trivial⟩
  | shift t k c => exact ⟨h, ne_of_lt h⟩

/-! ### The label box -/

/-- The label as `m` coordinates of `m` atoms: coordinate `j` is column `j`. -/
def cols (g : Matrix (Fin m) (Fin m) R) : Fin m → Fin m → R := fun j i => g i j

/-- Right multiplication by the transpose of a lower-triangular matrix is its ordered program. -/
theorem lower_route {E : Matrix (Fin m) (Fin m) R} (hE : LowerTriangular E)
    (g : Matrix (Fin m) (Fin m) R) :
    atomRun ((OrderedAffine.program E).map atomOp) (cols g) = cols (g * Eᵀ) := by
  funext j i
  have h : atomRun ((OrderedAffine.program E).map atomOp) (cols g) j i =
      OrderedAffine.run (OrderedAffine.program E) (fun t => cols g t i) j :=
    congrFun (atomRun_level (OrderedAffine.program E) (cols g) i) j
  rw [h, OrderedAffine.program_run hE]
  simp [cols, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]

/-- Right multiplication by the transpose of a full pivot matrix permutes the columns. -/
theorem pivot_route (L : List (Fin m × Fin m)) (hL : L.Nodup) (π : Fin m → Fin m)
    (hπ : ∀ j k, (j, k) ∈ L ↔ k = π j) (g : Matrix (Fin m) (Fin m) R) :
    cols (g * (pivotMatrix L : Matrix (Fin m) (Fin m) R)ᵀ) = fun j => cols g (π j) := by
  funext j i
  simp [cols, Matrix.mul_apply, pivotMatrix_apply L hL, hπ]

/-- A pivot list with distinct rows, distinct columns and `m` entries is a permutation. -/
theorem exists_perm (L : List (Fin m × Fin m)) (h₁ : (L.map Prod.fst).Nodup)
    (h₂ : (L.map Prod.snd).Nodup) (hlen : L.length = m) :
    ∃ π : Equiv.Perm (Fin m), ∀ j k, (j, k) ∈ L ↔ k = π j := by
  have hfin : (L.map Prod.fst).toFinset = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [List.toFinset_card_of_nodup h₁, List.length_map, hlen, Fintype.card_fin]
  have htot : ∀ j, ∃ k, (j, k) ∈ L := by
    intro j
    have hj : j ∈ (L.map Prod.fst).toFinset := hfin ▸ Finset.mem_univ j
    obtain ⟨⟨a, b⟩, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hj)
    exact ⟨b, hp⟩
  choose π hπ using htot
  have hinj : Function.Injective π := by
    intro j j' h
    have := List.inj_on_of_nodup_map h₂ (hπ j) (hπ j') h
    exact congrArg Prod.fst this
  refine ⟨Equiv.ofBijective π (Finite.injective_iff_bijective.mp hinj), fun j k => ⟨fun h => ?_, ?_⟩⟩
  · have := List.inj_on_of_nodup_map h₁ h (hπ j) rfl
    exact congrArg Prod.snd this
  · rintro rfl
    exact hπ j

/-- A permutation is a product of fewer exchanges than points it moves. -/
theorem exists_swaps : ∀ (c : ℕ) (π : Equiv.Perm (Fin m)), π.support.card = c →
    ∃ l : List {p : Fin m × Fin m // p.1 < p.2}, l.length ≤ c - 1 ∧
      π = (l.map fun p => Equiv.swap p.val.1 p.val.2).prod := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro π hc
    by_cases h1 : π = 1
    · exact ⟨[], by simp, by simp [h1]⟩
    · obtain ⟨x, hx⟩ : ∃ x, π x ≠ x := by
        by_contra hcon
        push Not at hcon
        exact h1 (Equiv.ext hcon)
      have hlt := Equiv.Perm.card_support_swap_mul hx
      have h2 := Equiv.Perm.two_le_card_support_of_ne_one h1
      obtain ⟨l, hl, hprod⟩ := ih _ (hc ▸ hlt) (Equiv.swap x (π x) * π) rfl
      obtain ⟨p, hp⟩ : ∃ p : {p : Fin m × Fin m // p.1 < p.2},
          Equiv.swap p.val.1 p.val.2 = Equiv.swap x (π x) := by
        rcases lt_or_gt_of_ne hx with h | h
        · exact ⟨⟨(π x, x), h⟩, Equiv.swap_comm _ _⟩
        · exact ⟨⟨(x, π x), h⟩, rfl⟩
      refine ⟨p :: l, ?_, ?_⟩
      · rw [List.length_cons]
        omega
      · rw [List.map_cons, List.prod_cons, hp, ← hprod, Equiv.swap_mul_self_mul]

/-- A column permutation is at most `m - 1` exchanges of two columns. -/
theorem swaps_le (π : Equiv.Perm (Fin m)) :
    ∃ l : List {p : Fin m × Fin m // p.1 < p.2}, l.length ≤ m - 1 ∧
      π = (l.map fun p => Equiv.swap p.val.1 p.val.2).prod := by
  obtain ⟨l, hl, hprod⟩ := exists_swaps _ π rfl
  have hle : π.support.card ≤ m := by
    simpa using Finset.card_le_univ π.support
  exact ⟨l, by omega, hprod⟩

/-! ### Routes -/

/-- A route with `σᵀ = E₁ Π E₂`: the program of `E₂`, the column permutation, the program of
`E₁`. -/
theorem route {σ E₁ E₂ : Matrix (Fin m) (Fin m) R} {L : List (Fin m × Fin m)}
    (h₁ : LowerTriangular E₁) (h₂ : LowerTriangular E₂) (hL : L.Nodup) (π : Fin m → Fin m)
    (hπ : ∀ j k, (j, k) ∈ L ↔ k = π j) (hσ : σᵀ = E₁ * pivotMatrix L * E₂)
    (g : Matrix (Fin m) (Fin m) R) :
    atomRun ((OrderedAffine.program E₁).map atomOp)
        (fun j => atomRun ((OrderedAffine.program E₂).map atomOp) (cols g) (π j)) =
      cols (g * σ) := by
  have hσ' : σ = E₂ᵀ * (pivotMatrix L : Matrix (Fin m) (Fin m) R)ᵀ * E₁ᵀ := by
    rw [← transpose_transpose σ, hσ]
    simp [transpose_mul, Matrix.mul_assoc]
  rw [lower_route h₂, ← pivot_route L hL π hπ (g * E₂ᵀ), lower_route h₁, hσ']
  simp [Matrix.mul_assoc]

/-- An invertible rational route runs over `ZMod (q ^ b)` for every large prime `q`: two legal
ordered passes around a column permutation. -/
theorem exists_route (σ : Matrix (Fin m) (Fin m) ℚ) (hσ : IsUnit σ) :
    ∃ D : Finset ℕ, ∀ q : ℕ, q.Prime → (∀ d ∈ D, d < q) → ∀ b : ℕ,
      ∃ (E₁ E₂ : Matrix (Fin m) (Fin m) (ZMod (q ^ b))) (π : Equiv.Perm (Fin m)),
        (∀ op ∈ OrderedAffine.program E₁, OrderedAffine.Legal op) ∧
        (∀ op ∈ OrderedAffine.program E₂, OrderedAffine.Legal op) ∧
        ∀ g : Matrix (Fin m) (Fin m) (ZMod (q ^ b)),
          atomRun ((OrderedAffine.program E₁).map atomOp)
              (fun j => atomRun ((OrderedAffine.program E₂).map atomOp) (cols g) (π j)) =
            cols (g * reduce (q ^ b) σ) := by
  obtain ⟨F⟩ := IntegerMultBounds.Swap.LowerTriangular.factorization σᵀ
  refine ⟨factorizationDenominators F, fun q hq hd b => ?_⟩
  obtain ⟨hlen, l₁, l₁', l₂, l₂', i₁, i₁', i₂, i₂', heq⟩ :=
    reduce_factorization_of_prime F hq hd b
  have hrank : F.L.length = m := by
    rw [hlen, rank_transpose, rank_of_isUnit σ hσ, Fintype.card_fin]
  obtain ⟨π, hπ⟩ := exists_perm F.L F.nodup₁ F.nodup₂ hrank
  refine ⟨reduce (q ^ b) F.E₁, reduce (q ^ b) F.E₂, π,
    OrderedAffine.program_legal l₁ (isUnit_iff_exists.mpr ⟨_, i₁, i₁'⟩),
    OrderedAffine.program_legal l₂ (isUnit_iff_exists.mpr ⟨_, i₂, i₂'⟩), fun g => ?_⟩
  exact route l₁ l₂ (F.nodup₁.of_map _) π hπ heq g

end IntegerMultBounds.MathlibTM2.Cover.Route
