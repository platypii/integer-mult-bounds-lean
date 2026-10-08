import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.Sort

/-! The algebra of the rational matrix shear (§4, Lemma 4.2). Two ordered groups
of fields `H` and `D` are updated. A pivot pair `(i, j)` adds `D_j` to `H_i`
using one interchange of the two fields and two updates of the later field by
the earlier one. A list of pivots adds `Π D` to `H`, where `Π` has a one at every
listed position, and a factorization `A = E₁ Π E₂` with invertible factors turns
this into `H ← H + A D` with exactly as many interchanges as pivots. A lower
triangular transformation is a sequence of coordinate updates in descending
order, each reading only its own and earlier coordinates. These are identities
over any commutative ring; the tape cost of each update and the choice of a
modulus are separate obligations. -/

namespace IntegerMultBounds.Swap.Shear

open Matrix Finset

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The `H` group and the `D` group of fields. -/
abbrev State (ι R : Type*) := (ι → R) × (ι → R)

/-- The field operations of the shear. The three pivot operations touch one
`H` field and one `D` field; the transformations act within a group. -/
inductive Op (ι R : Type*)
  | addToD (i j : ι)
  | subFromD (i j : ι)
  | interchange (i j : ι)
  | transformH (E : Matrix ι ι R)
  | transformD (E : Matrix ι ι R)

/-- `addToD`: `D_j ← D_j + H_i`; `subFromD`: `D_j ← H_i - D_j`; `interchange`
exchanges `H_i` and `D_j`; the transformations apply a matrix to one group. -/
def Op.run : Op ι R → State ι R → State ι R
  | .addToD i j, s => (s.1, Function.update s.2 j (s.2 j + s.1 i))
  | .subFromD i j, s => (s.1, Function.update s.2 j (s.1 i - s.2 j))
  | .interchange i j, s => (Function.update s.1 i (s.2 j), Function.update s.2 j (s.1 i))
  | .transformH E, s => (E *ᵥ s.1, s.2)
  | .transformD E, s => (s.1, E *ᵥ s.2)

def run (p : List (Op ι R)) (s : State ι R) : State ι R := p.foldl (fun s o => o.run s) s

@[simp] theorem run_nil (s : State ι R) : run [] s = s := rfl

@[simp] theorem run_cons (o : Op ι R) (p : List (Op ι R)) (s : State ι R) :
    run (o :: p) s = run p (o.run s) := rfl

theorem run_append (p q : List (Op ι R)) (s : State ι R) :
    run (p ++ q) s = run q (run p s) := List.foldl_append

def Op.isInterchange : Op ι R → Bool
  | .interchange _ _ => true
  | _ => false

/-- The number of interchanges of a program; the other operations are linear. -/
def interchanges (p : List (Op ι R)) : ℕ := (p.filter Op.isInterchange).length

omit [Fintype ι] [DecidableEq ι] [CommRing R] in
theorem interchanges_append (p q : List (Op ι R)) :
    interchanges (p ++ q) = interchanges p + interchanges q := by
  simp [interchanges, List.filter_append]

section Pivot

/-- One interchange and two later-field updates realize `H_i ← H_i + D_j`. -/
def pivotProgram (i j : ι) : List (Op ι R) := [.addToD i j, .interchange i j, .subFromD i j]

theorem pivotProgram_run (i j : ι) (s : State ι R) :
    run (pivotProgram i j) s = (Function.update s.1 i (s.1 i + s.2 j), s.2) := by
  simp only [pivotProgram, run_cons, run_nil, Op.run, Function.update_self, Function.update_idem,
    add_comm]
  rw [add_sub_cancel_left, Function.update_eq_self]

omit [Fintype ι] [DecidableEq ι] [CommRing R] in
@[simp] theorem pivotProgram_interchanges (i j : ι) :
    interchanges (pivotProgram (R := R) i j) = 1 := rfl

theorem pivotProgram_run_eq (i j : ι) (s : State ι R) :
    run (pivotProgram i j) s = (s.1 + (single i j 1 : Matrix ι ι R) *ᵥ s.2, s.2) := by
  rw [pivotProgram_run, single_mulVec]
  congr 1
  ext k
  by_cases hk : k = i
  · subst hk; simp
  · simp [hk]

/-- The matrix with a one at every listed position. -/
def pivotMatrix : List (ι × ι) → Matrix ι ι R
  | [] => 0
  | p :: rest => single p.1 p.2 1 + pivotMatrix rest

def pivotsProgram : List (ι × ι) → List (Op ι R)
  | [] => []
  | p :: rest => pivotProgram p.1 p.2 ++ pivotsProgram rest

/-- A pivot list adds `Π D` to `H`, where `Π` is its pivot matrix. -/
theorem pivotsProgram_run (L : List (ι × ι)) (s : State ι R) :
    run (pivotsProgram L) s = (s.1 + pivotMatrix L *ᵥ s.2, s.2) := by
  induction L generalizing s with
  | nil => simp [pivotsProgram, pivotMatrix]
  | cons p rest ih =>
    rw [pivotsProgram, run_append, pivotProgram_run_eq, ih]
    simp [pivotMatrix, add_mulVec, add_assoc]

omit [Fintype ι] [DecidableEq ι] [CommRing R] in
/-- Exactly one interchange per pivot. -/
theorem pivotsProgram_interchanges (L : List (ι × ι)) :
    interchanges (pivotsProgram (R := R) L) = L.length := by
  induction L with
  | nil => rfl
  | cons p rest ih =>
    rw [pivotsProgram, interchanges_append, pivotProgram_interchanges, ih, List.length_cons]
    omega

end Pivot

section Factorized

/-- The shear `H ← H + E₁ Π E₂ D`: transform `D` by `E₂` and `H` by `E₁'`, add
`Π D` to `H`, then transform `H` by `E₁` and `D` by `E₂'`. -/
def shearProgram (E₁ E₁' E₂ E₂' : Matrix ι ι R) (L : List (ι × ι)) : List (Op ι R) :=
  [.transformD E₂, .transformH E₁'] ++ pivotsProgram L ++ [.transformH E₁, .transformD E₂']

theorem shearProgram_run (E₁ E₁' E₂ E₂' : Matrix ι ι R) (h₁ : E₁ * E₁' = 1) (h₂ : E₂' * E₂ = 1)
    (L : List (ι × ι)) (s : State ι R) :
    run (shearProgram E₁ E₁' E₂ E₂' L) s = (s.1 + (E₁ * pivotMatrix L * E₂) *ᵥ s.2, s.2) := by
  simp only [shearProgram, run_append, run_cons, run_nil, Op.run, pivotsProgram_run]
  simp only [mulVec_add, mulVec_mulVec, h₁, h₂, one_mulVec]
  rw [Matrix.mul_assoc]

omit [Fintype ι] [DecidableEq ι] [CommRing R] in
/-- The interchange count is the number of ones of the pivot matrix. -/
theorem shearProgram_interchanges (E₁ E₁' E₂ E₂' : Matrix ι ι R) (L : List (ι × ι)) :
    interchanges (shearProgram E₁ E₁' E₂ E₂' L) = L.length := by
  simp only [shearProgram, interchanges_append, pivotsProgram_interchanges]
  simp [interchanges, Op.isInterchange]

end Factorized

section Triangular
variable [LinearOrder ι]

/-- `E i j = 0` above the diagonal. -/
def LowerTriangular (E : Matrix ι ι R) : Prop := ∀ i j, i < j → E i j = 0

omit [DecidableEq ι] in
/-- Row `i` of a lower triangular matrix reads only coordinate `i` and earlier
coordinates: the target field follows its control fields. -/
theorem lower_row_apply {E : Matrix ι ι R} (hE : LowerTriangular E) (x : ι → R) (i : ι) :
    (E *ᵥ x) i = E i i * x i + ∑ j ∈ univ.filter (· < i), E i j * x j := by
  simp only [mulVec, dotProduct]
  rw [← sum_filter_add_sum_filter_not univ (· < i), add_comm]
  congr 1
  rw [sum_eq_single i]
  · intro j hj hji
    simp only [mem_filter, mem_univ, true_and, not_lt] at hj
    rw [hE i j (lt_of_le_of_ne hj (Ne.symm hji)), zero_mul]
  · intro h
    simp at h

/-- Replace coordinate `i` by row `i` of `E` applied to the current vector. -/
def coordinateUpdate (E : Matrix ι ι R) (x : ι → R) (i : ι) : ι → R :=
  Function.update x i ((E *ᵥ x) i)

def orderedUpdates (E : Matrix ι ι R) (l : List ι) (x : ι → R) : ι → R :=
  l.foldl (coordinateUpdate E) x

omit [LinearOrder ι] in
theorem mulVec_update_of_zero (E : Matrix ι ι R) {j i : ι} (h : E j i = 0) (x : ι → R) (c : R) :
    (E *ᵥ Function.update x i c) j = (E *ᵥ x) j := by
  simp only [mulVec, dotProduct]
  apply sum_congr rfl
  intro k _
  by_cases hk : k = i
  · subst hk; rw [h, zero_mul, zero_mul]
  · rw [Function.update_of_ne hk]

/-- Updating coordinates in strictly descending order, each update sees the
original values of all coordinates it reads. -/
theorem orderedUpdates_apply {E : Matrix ι ι R} (hE : LowerTriangular E) :
    ∀ (l : List ι), l.Pairwise (· > ·) → ∀ x : ι → R,
      orderedUpdates E l x = fun j => if j ∈ l then (E *ᵥ x) j else x j := by
  intro l
  induction l with
  | nil => intro _ x; funext j; simp [orderedUpdates]
  | cons i rest ih =>
    intro hl x
    rw [List.pairwise_cons] at hl
    have hstep : orderedUpdates E (i :: rest) x = orderedUpdates E rest (coordinateUpdate E x i) :=
      rfl
    rw [hstep, ih hl.2]
    funext j
    by_cases hj : j ∈ rest
    · have hji : i > j := hl.1 j hj
      simp only [hj, ite_true, List.mem_cons, or_true, coordinateUpdate]
      exact mulVec_update_of_zero E (hE j i hji) x _
    · simp only [hj, ite_false, List.mem_cons, or_false, coordinateUpdate]
      by_cases hji : j = i
      · subst hji; simp
      · simp [hji]

/-- Every index in strictly descending order. -/
def descending (ι : Type*) [Fintype ι] [LinearOrder ι] : List ι := (univ.sort).reverse

omit [DecidableEq ι] in
theorem descending_pairwise : (descending ι).Pairwise (· > ·) := by
  unfold descending
  rw [List.pairwise_reverse]
  exact List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort _)

omit [DecidableEq ι] in
theorem mem_descending (i : ι) : i ∈ descending ι := by
  unfold descending
  rw [List.mem_reverse, Finset.mem_sort]
  exact mem_univ i

/-- A lower triangular transformation is the descending sequence of its
coordinate updates. -/
theorem lower_transform_eq {E : Matrix ι ι R} (hE : LowerTriangular E) (x : ι → R) :
    orderedUpdates E (descending ι) x = E *ᵥ x := by
  rw [orderedUpdates_apply hE _ descending_pairwise]
  funext j
  simp [mem_descending]

end Triangular

end IntegerMultBounds.Swap.Shear
