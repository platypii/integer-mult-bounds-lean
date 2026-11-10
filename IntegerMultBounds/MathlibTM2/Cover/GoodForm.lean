module

public import IntegerMultBounds.MathlibTM2.Cover.Weighted
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing

/-!
# The good normal form over a commutative ring

At a cover label the projector of a move has entries in the atom ring `Z/q^w`, which is not a
field. `good_form`: if `P = A B` factors through `r` coordinates and its leading principal minors
of sizes `1..r` are units, then `P C = L Δ Π_r R` with unit lower-triangular `L` and `R`, unit
pivots `Δ`, and `Π_r` the reversed pivots. This is the hypothesis of
`Weighted.weighted_good_child`.

The proof is elimination without pivot normalization.

* `Stage P k`: `P = L M U` with unit triangular `L`, `U` and their inverses, where the rows and
  columns of `M` before `k` are diagonal with unit entries.
* `pivot_isUnit`: unit triangular factors keep the leading minors (`lead_lower_mul`,
  `lead_mul_upper`), and the leading minor of `M` of size `k+1` is the product of its diagonal,
  so the next pivot is a unit.
* `next`: one elimination step (`elim_eq`, `elim_cleared`).
* `rest_zero`: after `r` steps the factorization through `r` coordinates forces the remaining
  block of `M` to vanish over the ring itself.
* `good_move`: for an idempotent `P`, the weighted reversed exchange is unit triangular adapters
  conjugated by the weights, two shears, and one weighted reversed child of rank `r`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.GoodForm

open Matrix
open IntegerMultBounds.Swap.Shear (pivotMatrix LowerTriangular)
open IntegerMultBounds.Swap.PivotRank (pivotMatrix_apply)
open IntegerMultBounds.MathlibTM2.M8.Exchange (transform cross kMat)
open IntegerMultBounds.MathlibTM2.M8.ReversedExchange
  (rev rev_mul_rev rev_mul_rev_mul revPivots revPivots_fst mem_revPivots revExchangeOf)
open IntegerMultBounds.Swap.Shear (State)

variable {m : ℕ} {R : Type*} [CommRing R]

/-! ### Unit triangular matrices -/

/-- Lower triangular with unit diagonal. -/
def UnitLower (L : Matrix (Fin m) (Fin m) R) : Prop := LowerTriangular L ∧ ∀ i, L i i = 1

/-- Upper triangular with unit diagonal. -/
def UnitUpper (U : Matrix (Fin m) (Fin m) R) : Prop := UnitLower Uᵀ

theorem unitLower_one : UnitLower (1 : Matrix (Fin m) (Fin m) R) :=
  ⟨fun _ _ h => one_apply_ne h.ne, fun _ => one_apply_eq _⟩

theorem unitUpper_one : UnitUpper (1 : Matrix (Fin m) (Fin m) R) := by
  rw [UnitUpper, transpose_one]
  exact unitLower_one

theorem UnitLower.mul {L N : Matrix (Fin m) (Fin m) R} (hL : UnitLower L) (hN : UnitLower N) :
    UnitLower (L * N) := by
  constructor
  · intro i j hij
    rw [mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : i < l
    · rw [hL.1 i l hl, zero_mul]
    · rw [hN.1 l j (lt_of_le_of_lt (not_lt.mp hl) hij), mul_zero]
  · intro i
    rw [mul_apply, Finset.sum_eq_single i]
    · rw [hL.2, hN.2, mul_one]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hN.1 l i h, mul_zero]
      · rw [hL.1 i l h, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h

theorem UnitUpper.mul {U V : Matrix (Fin m) (Fin m) R} (hU : UnitUpper U) (hV : UnitUpper V) :
    UnitUpper (U * V) := by
  rw [UnitUpper, transpose_mul]
  exact UnitLower.mul hV hU

/-! ### Leading minors -/

/-- The leading principal submatrix of size `n`. -/
def lead (n : ℕ) (h : n ≤ m) (A : Matrix (Fin m) (Fin m) R) : Matrix (Fin n) (Fin n) R :=
  A.submatrix (Fin.castLE h) (Fin.castLE h)

theorem lead_lower_mul (n : ℕ) (h : n ≤ m) {L : Matrix (Fin m) (Fin m) R} (hL : LowerTriangular L)
    (A : Matrix (Fin m) (Fin m) R) : lead n h (L * A) = lead n h L * lead n h A := by
  ext i j
  simp only [lead, submatrix_apply, mul_apply]
  refine (Finset.sum_of_injOn (Fin.castLE h) (Fin.castLE_injective h).injOn
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) ?_ (fun _ _ => rfl)).symm
  intro l _ hl
  have hln : n ≤ l.val := by
    by_contra hlt
    exact hl ⟨⟨l.val, not_le.mp hlt⟩, Finset.mem_coe.mpr (Finset.mem_univ _), Fin.ext rfl⟩
  rw [hL _ _ (show (Fin.castLE h i).val < l.val from lt_of_lt_of_le i.isLt hln), zero_mul]

theorem lead_mul_upper (n : ℕ) (h : n ≤ m) {U : Matrix (Fin m) (Fin m) R}
    (hU : LowerTriangular Uᵀ) (A : Matrix (Fin m) (Fin m) R) :
    lead n h (A * U) = lead n h A * lead n h U := by
  ext i j
  have h1 := congrFun (congrFun (lead_lower_mul n h hU Aᵀ) j) i
  simp only [lead, submatrix_apply, mul_apply, transpose_apply] at h1 ⊢
  have e1 : ∑ l, A (Fin.castLE h i) l * U l (Fin.castLE h j) =
      ∑ l, U l (Fin.castLE h j) * A (Fin.castLE h i) l :=
    Finset.sum_congr rfl fun l _ => mul_comm _ _
  have e2 : ∑ l, U (Fin.castLE h l) (Fin.castLE h j) * A (Fin.castLE h i) (Fin.castLE h l) =
      ∑ l, A (Fin.castLE h i) (Fin.castLE h l) * U (Fin.castLE h l) (Fin.castLE h j) :=
    Finset.sum_congr rfl fun l _ => mul_comm _ _
  rw [e1, h1, e2]

theorem det_lead_lower (n : ℕ) (h : n ≤ m) {L : Matrix (Fin m) (Fin m) R} (hL : UnitLower L) :
    (lead n h L).det = 1 := by
  have htri : (lead n h L).IsLowerTriangular := fun i j hij =>
    hL.1 _ _ (show (Fin.castLE h i).val < (Fin.castLE h j).val from
      OrderDual.toDual_lt_toDual.mp hij)
  rw [det_of_isLowerTriangular _ htri]
  exact Finset.prod_eq_one fun i _ => hL.2 _

theorem det_lead_upper (n : ℕ) (h : n ≤ m) {U : Matrix (Fin m) (Fin m) R} (hU : UnitUpper U) :
    (lead n h U).det = 1 :=
  (det_transpose _).symm.trans (det_lead_lower n h hU)

/-! ### One elimination step -/

/-- Rows and columns before `k` are diagonal. -/
def Cleared (k : ℕ) (M : Matrix (Fin m) (Fin m) R) : Prop :=
  ∀ i j : Fin m, i.val < k ∨ j.val < k → i ≠ j → M i j = 0

/-- The matrix with the column `n` in position `k`. -/
def colMat (k : Fin m) (n : Fin m → R) : Matrix (Fin m) (Fin m) R :=
  of fun i l => if l = k then n i else 0

/-- The matrix with the row `n` in position `k`. -/
def rowMat (k : Fin m) (n : Fin m → R) : Matrix (Fin m) (Fin m) R :=
  of fun l j => if l = k then n j else 0

theorem rowMat_transpose (k : Fin m) (n : Fin m → R) : (rowMat k n)ᵀ = colMat k n := rfl

theorem colMat_mul (k : Fin m) (n : Fin m → R) (Y : Matrix (Fin m) (Fin m) R) (i j : Fin m) :
    (colMat k n * Y) i j = n i * Y k j := by
  rw [mul_apply, Finset.sum_eq_single k]
  · simp [colMat]
  · intro l _ hl
    simp [colMat, hl]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mul_rowMat (k : Fin m) (n : Fin m → R) (X : Matrix (Fin m) (Fin m) R) (i j : Fin m) :
    (X * rowMat k n) i j = X i k * n j := by
  rw [mul_apply, Finset.sum_eq_single k]
  · simp [rowMat]
  · intro l _ hl
    simp [rowMat, hl]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem colMat_mul_colMat (k : Fin m) (n n' : Fin m → R) (hn : n' k = 0) :
    colMat k n * colMat k n' = 0 := by
  ext i j
  rw [colMat_mul]
  by_cases hj : j = k <;> simp [colMat, hj, hn]

theorem rowMat_mul_rowMat (k : Fin m) (n n' : Fin m → R) (hn : n k = 0) :
    rowMat k n * rowMat k n' = 0 := by
  ext i j
  rw [mul_rowMat]
  by_cases hi : i = k <;> simp [rowMat, hi, hn]

theorem add_mul_sub {N : Matrix (Fin m) (Fin m) R} (hN : N * N = 0) :
    (1 + N) * (1 - N) = 1 ∧ (1 - N) * (1 + N) = 1 := by
  have h1 : (1 + N) * (1 - N) = 1 - N * N := by noncomm_ring
  have h2 : (1 - N) * (1 + N) = 1 - N * N := by noncomm_ring
  rw [h1, h2, hN, sub_zero]
  exact ⟨rfl, rfl⟩

theorem unitLower_add_colMat (k : Fin m) (n : Fin m → R) (hn : ∀ i, i ≤ k → n i = 0) :
    UnitLower (1 + colMat k n) := by
  constructor
  · intro i j hij
    rw [Matrix.add_apply, one_apply_ne hij.ne, zero_add]
    by_cases hj : j = k
    · subst hj
      simp [colMat, hn i hij.le]
    · simp [colMat, hj]
  · intro i
    rw [Matrix.add_apply, one_apply_eq]
    by_cases hi : i = k
    · subst hi
      simp [colMat, hn i le_rfl]
    · simp [colMat, hi]

theorem unitLower_sub_colMat (k : Fin m) (n : Fin m → R) (hn : ∀ i, i ≤ k → n i = 0) :
    UnitLower (1 - colMat k n) := by
  have h : 1 - colMat k n = 1 + colMat k (fun i => -n i) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, colMat, of_apply]
    split_ifs <;> ring
  rw [h]
  exact unitLower_add_colMat k _ fun i hi => by rw [hn i hi, neg_zero]

theorem unitUpper_add_rowMat (k : Fin m) (n : Fin m → R) (hn : ∀ i, i ≤ k → n i = 0) :
    UnitUpper (1 + rowMat k n) := by
  rw [UnitUpper, transpose_add, transpose_one, rowMat_transpose]
  exact unitLower_add_colMat k n hn

theorem unitUpper_sub_rowMat (k : Fin m) (n : Fin m → R) (hn : ∀ i, i ≤ k → n i = 0) :
    UnitUpper (1 - rowMat k n) := by
  rw [UnitUpper, transpose_sub, transpose_one, rowMat_transpose]
  exact unitLower_sub_colMat k n hn

/-- The multipliers of column `k`. -/
def elimL (k : Fin m) (M : Matrix (Fin m) (Fin m) R) (p' : R) : Fin m → R :=
  fun i => if i = k then 0 else M i k * p'

/-- The multipliers of row `k`. -/
def elimU (k : Fin m) (M : Matrix (Fin m) (Fin m) R) (p' : R) : Fin m → R :=
  fun j => if j = k then 0 else p' * M k j

/-- The matrix after clearing row and column `k` around the pivot `M k k`. -/
def elimM (k : Fin m) (M : Matrix (Fin m) (Fin m) R) (p' : R) : Matrix (Fin m) (Fin m) R :=
  of fun i j => if i = k ∨ j = k then (if i = j then M k k else 0)
    else M i j - M i k * p' * M k j

theorem elimL_zero (k : Fin m) {M : Matrix (Fin m) (Fin m) R} (hM : Cleared k.val M) (p' : R)
    (i : Fin m) (hi : i ≤ k) : elimL k M p' i = 0 := by
  by_cases hik : i = k
  · simp [elimL, hik]
  · have hlt : i.val < k.val := lt_of_le_of_ne hi fun h => hik (Fin.ext h)
    simp [elimL, hik, hM i k (Or.inl hlt) hik]

theorem elimU_zero (k : Fin m) {M : Matrix (Fin m) (Fin m) R} (hM : Cleared k.val M) (p' : R)
    (j : Fin m) (hj : j ≤ k) : elimU k M p' j = 0 := by
  by_cases hjk : j = k
  · simp [elimU, hjk]
  · have hlt : j.val < k.val := lt_of_le_of_ne hj fun h => hjk (Fin.ext h)
    simp [elimU, hjk, hM k j (Or.inr hlt) fun h => hjk h.symm]

/-- The step undone: `M` is the cleared matrix between the two unit triangular factors. -/
theorem elim_eq (k : Fin m) (M : Matrix (Fin m) (Fin m) R) (p' : R) (hp : M k k * p' = 1) :
    (1 + colMat k (elimL k M p')) * elimM k M p' * (1 + rowMat k (elimU k M p')) = M := by
  ext i j
  simp only [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply,
    mul_rowMat, colMat_mul]
  by_cases hi : i = k
  · by_cases hj : j = k
    · subst hi
      subst hj
      simp [elimM, elimL, elimU]
    · subst hi
      have hj' : ¬i = j := fun h => hj h.symm
      simp only [elimM, elimL, elimU, of_apply, hj, hj', true_or, or_true, ↓reduceIte]
      linear_combination M i j * hp
  · by_cases hj : j = k
    · subst hj
      simp only [elimM, elimL, elimU, of_apply, hi, or_true, ↓reduceIte]
      linear_combination M i j * hp
    · have hj' : ¬k = j := fun h => hj h.symm
      simp only [elimM, elimL, elimU, of_apply, hi, hj, hj', or_self, or_true, true_or, ↓reduceIte]
      linear_combination M i k * p' * M k j * hp

theorem elim_cleared (k : Fin m) {M : Matrix (Fin m) (Fin m) R} (hM : Cleared k.val M) (p' : R) :
    Cleared (k.val + 1) (elimM k M p') := by
  intro i j hlt hne
  by_cases h : i = k ∨ j = k
  · simp [elimM, h, hne]
  · have hi : i ≠ k := fun e => h (Or.inl e)
    have hj : j ≠ k := fun e => h (Or.inr e)
    have hiv : i.val ≠ k.val := fun e => hi (Fin.ext e)
    have hjv : j.val ≠ k.val := fun e => hj (Fin.ext e)
    simp only [elimM, of_apply, h, ↓reduceIte]
    rcases hlt with hlt | hlt
    · have hik : i.val < k.val := by omega
      rw [hM i j (Or.inl hik) hne, hM i k (Or.inl hik) hi]
      ring
    · have hjk : j.val < k.val := by omega
      rw [hM i j (Or.inr hjk) hne, hM k j (Or.inr hjk) fun e => hj e.symm]
      ring

theorem elim_diag (k : Fin m) {M : Matrix (Fin m) (Fin m) R} (hM : Cleared k.val M) (p' : R)
    (i : Fin m) (hi : i.val < k.val + 1) : elimM k M p' i i = M i i := by
  by_cases hik : i = k
  · simp [elimM, hik]
  · have hlt : i.val < k.val := by
      have : i.val ≠ k.val := fun e => hik (Fin.ext e)
      omega
    simp [elimM, hik, hM i k (Or.inl hlt) hik]

/-! ### Elimination -/

/-- `P = L M U` with unit triangular `L`, `U` and their inverses. The rows and columns of `M`
before `k` are diagonal with unit entries. -/
structure Stage (P : Matrix (Fin m) (Fin m) R) (k : ℕ) where
  L : Matrix (Fin m) (Fin m) R
  L' : Matrix (Fin m) (Fin m) R
  U : Matrix (Fin m) (Fin m) R
  U' : Matrix (Fin m) (Fin m) R
  M : Matrix (Fin m) (Fin m) R
  lower : UnitLower L
  lower' : UnitLower L'
  upper : UnitUpper U
  upper' : UnitUpper U'
  left : L * L' = 1
  left' : L' * L = 1
  right : U * U' = 1
  right' : U' * U = 1
  eq : P = L * M * U
  cleared : Cleared k M
  unit : ∀ i : Fin m, i.val < k → IsUnit (M i i)

/-- The next pivot is a unit when the next leading minor of `P` is. -/
theorem pivot_isUnit {P : Matrix (Fin m) (Fin m) R} {k : ℕ} (S : Stage P k) (hk : k < m)
    (hminor : IsUnit (lead (k + 1) hk P).det) : IsUnit (S.M ⟨k, hk⟩ ⟨k, hk⟩) := by
  have hdiag : lead (k + 1) hk S.M =
      diagonal fun i => S.M (Fin.castLE hk i) (Fin.castLE hk i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq]
      rfl
    · rw [diagonal_apply_ne _ hij]
      have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
      have hi := i.isLt
      have hj := j.isLt
      refine S.cleared _ _ ?_ fun h => hij (Fin.castLE_injective hk h)
      show i.val < k ∨ j.val < k
      omega
  rw [S.eq, lead_mul_upper _ _ S.upper.1, lead_lower_mul _ _ S.lower.1, det_mul, det_mul,
    det_lead_lower _ _ S.lower, det_lead_upper _ _ S.upper, one_mul, mul_one, hdiag,
    det_diagonal] at hminor
  exact IsUnit.prod_iff.mp hminor (Fin.last k) (Finset.mem_univ _)

/-- One elimination step. -/
theorem next {P : Matrix (Fin m) (Fin m) R} {k : ℕ} (S : Stage P k) (hk : k < m)
    (hu : IsUnit (S.M ⟨k, hk⟩ ⟨k, hk⟩)) : Nonempty (Stage P (k + 1)) := by
  obtain ⟨p', hp⟩ := hu.exists_right_inv
  have hcl : Cleared (⟨k, hk⟩ : Fin m).val S.M := S.cleared
  have hnL := elimL_zero ⟨k, hk⟩ hcl p'
  have hnU := elimU_zero ⟨k, hk⟩ hcl p'
  obtain ⟨hc, hc'⟩ := add_mul_sub
    (colMat_mul_colMat ⟨k, hk⟩ (elimL ⟨k, hk⟩ S.M p') (elimL ⟨k, hk⟩ S.M p') (hnL _ le_rfl))
  obtain ⟨hr, hr'⟩ := add_mul_sub
    (rowMat_mul_rowMat ⟨k, hk⟩ (elimU ⟨k, hk⟩ S.M p') (elimU ⟨k, hk⟩ S.M p') (hnU _ le_rfl))
  refine ⟨{
    L := S.L * (1 + colMat ⟨k, hk⟩ (elimL ⟨k, hk⟩ S.M p'))
    L' := (1 - colMat ⟨k, hk⟩ (elimL ⟨k, hk⟩ S.M p')) * S.L'
    U := (1 + rowMat ⟨k, hk⟩ (elimU ⟨k, hk⟩ S.M p')) * S.U
    U' := S.U' * (1 - rowMat ⟨k, hk⟩ (elimU ⟨k, hk⟩ S.M p'))
    M := elimM ⟨k, hk⟩ S.M p'
    lower := S.lower.mul (unitLower_add_colMat _ _ hnL)
    lower' := (unitLower_sub_colMat _ _ hnL).mul S.lower'
    upper := (unitUpper_add_rowMat _ _ hnU).mul S.upper
    upper' := S.upper'.mul (unitUpper_sub_rowMat _ _ hnU)
    left := ?_
    left' := ?_
    right := ?_
    right' := ?_
    eq := ?_
    cleared := elim_cleared ⟨k, hk⟩ hcl p'
    unit := fun i hi => ?_ }⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 + colMat _ _), hc, Matrix.one_mul, S.left]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc S.L', S.left', Matrix.one_mul, hc']
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc S.U, S.right, Matrix.one_mul, hr]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 - rowMat _ _), hr', Matrix.one_mul, S.right']
  · have h := S.eq
    rw [← elim_eq ⟨k, hk⟩ S.M p' hp] at h
    exact h.trans (by simp only [Matrix.mul_assoc])
  · rw [elim_diag ⟨k, hk⟩ hcl p' i hi]
    by_cases hik : i.val < k
    · exact S.unit i hik
    · have hi' : i = ⟨k, hk⟩ := Fin.ext (show i.val = k by have : i.val < k + 1 := hi; omega)
      rw [hi']
      exact hu

/-- Elimination runs for `r` steps when the leading minors of sizes `1..r` are units. -/
theorem stage (P : Matrix (Fin m) (Fin m) R) (r : ℕ) (hr : r ≤ m)
    (hminor : ∀ k (hk : k < r), IsUnit (lead (k + 1) (lt_of_lt_of_le hk hr) P).det) :
    ∀ k, k ≤ r → Nonempty (Stage P k) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨{
      L := 1, L' := 1, U := 1, U' := 1, M := P
      lower := unitLower_one, lower' := unitLower_one
      upper := unitUpper_one, upper' := unitUpper_one
      left := Matrix.one_mul 1, left' := Matrix.one_mul 1
      right := Matrix.one_mul 1, right' := Matrix.one_mul 1
      eq := by rw [Matrix.one_mul, Matrix.mul_one]
      cleared := fun i j h => absurd h (by omega)
      unit := fun i h => absurd h (Nat.not_lt_zero _) }⟩
  | succ k ih =>
    intro hk
    obtain ⟨S⟩ := ih (by omega)
    exact next S (lt_of_lt_of_le hk hr) (pivot_isUnit S _ (hminor k hk))

/-- After `r` steps, a factorization of `P` through `r` coordinates leaves nothing in the rows
from `r` on. -/
theorem rest_zero {P : Matrix (Fin m) (Fin m) R} {r : ℕ} (S : Stage P r) (hr : r ≤ m)
    (A : Matrix (Fin m) (Fin r) R) (B : Matrix (Fin r) (Fin m) R) (hP : P = A * B)
    (i j : Fin m) (hi : r ≤ i.val) : S.M i j = 0 := by
  have hM : S.L' * P * S.U' = S.M := by
    have h : S.L' * P * S.U' = S.L' * (S.L * S.M * S.U) * S.U' :=
      congrArg (fun X => S.L' * X * S.U') S.eq
    rw [h]
    simp only [Matrix.mul_assoc]
    rw [S.right, Matrix.mul_one, ← Matrix.mul_assoc, S.left', Matrix.one_mul]
  have hAB : S.M = (S.L' * A) * (B * S.U') := by
    have h : S.L' * P * S.U' = S.L' * (A * B) * S.U' :=
      congrArg (fun X => S.L' * X * S.U') hP
    rw [← hM, h]
    simp only [Matrix.mul_assoc]
  have hentry (a b : Fin m) : S.M a b = ∑ l, (S.L' * A) a l * (B * S.U') l b := by
    rw [hAB, mul_apply]
  have hT : (S.L' * A).submatrix (Fin.castLE hr) id * (B * S.U').submatrix id (Fin.castLE hr) =
      diagonal fun a => S.M (Fin.castLE hr a) (Fin.castLE hr a) := by
    ext a b
    have e : ((S.L' * A).submatrix (Fin.castLE hr) id *
        (B * S.U').submatrix id (Fin.castLE hr)) a b = S.M (Fin.castLE hr a) (Fin.castLE hr b) :=
      (hentry _ _).symm
    rw [e]
    by_cases hab : a = b
    · subst hab
      rw [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ hab]
      exact S.cleared _ _ (Or.inl a.isLt) fun h => hab (Fin.castLE_injective hr h)
  have hdet : IsUnit ((B * S.U').submatrix id (Fin.castLE hr)).det := by
    have h := congrArg det hT
    rw [det_mul, det_diagonal] at h
    have hprod : IsUnit (∏ a : Fin r, S.M (Fin.castLE hr a) (Fin.castLE hr a)) :=
      IsUnit.prod_iff.mpr fun a _ => S.unit _ a.isLt
    rw [← h] at hprod
    exact isUnit_of_mul_isUnit_right hprod
  have hv : (fun l => (S.L' * A) i l) ᵥ* (B * S.U').submatrix id (Fin.castLE hr) = 0 := by
    funext b
    have e : ((fun l => (S.L' * A) i l) ᵥ* (B * S.U').submatrix id (Fin.castLE hr)) b =
        S.M i (Fin.castLE hr b) := (hentry _ _).symm
    rw [e]
    refine S.cleared _ _ (Or.inr b.isLt) fun h => ?_
    have hval : i.val = b.val := congrArg Fin.val h
    have := b.isLt
    omega
  have hzero : (fun l => (S.L' * A) i l) = 0 := by
    have h : (fun l => (S.L' * A) i l) =
        ((fun l => (S.L' * A) i l) ᵥ* (B * S.U').submatrix id (Fin.castLE hr)) ᵥ*
          ((B * S.U').submatrix id (Fin.castLE hr))⁻¹ := by
      rw [vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, vecMul_one]
    rw [hv, zero_vecMul] at h
    exact h
  rw [hentry]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [show (S.L' * A) i l = 0 from congrFun hzero l, zero_mul]

/-! ### The reversed frame -/

theorem rev_mul_apply (X : Matrix (Fin m) (Fin m) R) (i j : Fin m) :
    ((rev m : Matrix (Fin m) (Fin m) R) * X) i j = X i.rev j := by
  rw [mul_apply, Finset.sum_eq_single i.rev]
  · simp [rev]
  · intro a _ ha
    simp [rev, ha]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mul_rev_apply (X : Matrix (Fin m) (Fin m) R) (i j : Fin m) :
    (X * (rev m : Matrix (Fin m) (Fin m) R)) i j = X i j.rev := by
  rw [mul_apply, Finset.sum_eq_single j.rev]
  · simp [rev]
  · intro a _ ha
    have hne : j ≠ a.rev := fun h => ha (by rw [h, Fin.rev_rev])
    simp [rev, hne]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Reversal turns unit upper triangular into unit lower triangular. -/
theorem unitLower_rev_conj {U : Matrix (Fin m) (Fin m) R} (hU : UnitUpper U) :
    UnitLower ((rev m : Matrix (Fin m) (Fin m) R) * U * rev m) := by
  constructor
  · intro i j hij
    rw [mul_rev_apply, rev_mul_apply]
    exact hU.1 j.rev i.rev (Fin.rev_lt_rev.mpr hij)
  · intro i
    rw [mul_rev_apply, rev_mul_apply]
    exact hU.2 i.rev

/-- **The good normal form.** If `P` factors through `r` coordinates and its leading principal
minors of sizes `1..r` are units, then `P C = L Δ Π_r R` with unit lower-triangular `L`, `R`,
their inverses, and unit pivots `Δ`. -/
theorem good_form (P : Matrix (Fin m) (Fin m) R) (r : ℕ) (hr : r ≤ m)
    (A : Matrix (Fin m) (Fin r) R) (B : Matrix (Fin r) (Fin m) R) (hP : P = A * B)
    (hminor : ∀ k (hk : k < r), IsUnit (lead (k + 1) (lt_of_lt_of_le hk hr) P).det) :
    ∃ (L L' R' R'' : Matrix (Fin m) (Fin m) R) (δ δ' : Fin m → R),
      UnitLower L ∧ UnitLower L' ∧ UnitLower R' ∧ UnitLower R'' ∧
      L * L' = 1 ∧ L' * L = 1 ∧ R' * R'' = 1 ∧ R'' * R' = 1 ∧ (∀ i, δ i * δ' i = 1) ∧
      P * rev m = L * diagonal δ * pivotMatrix (revPivots m r) * R' := by
  obtain ⟨S⟩ := stage P r hr hminor r le_rfl
  have hnodup : (revPivots m r).Nodup := (revPivots_fst m r).of_map _
  have hMdiag : S.M = diagonal fun i => if i.val < r then S.M i i else 0 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq]
      by_cases hi : i.val < r
      · rw [ite_eq_left hi]
      · rw [ite_eq_right hi]
        exact rest_zero S hr A B hP i i (not_lt.mp hi)
    · rw [diagonal_apply_ne _ hij]
      by_cases hi : i.val < r
      · exact S.cleared i j (Or.inl hi) hij
      · exact rest_zero S hr A B hP i j (not_lt.mp hi)
  have hkey : (diagonal fun i => if i.val < r then S.M i i else 0) * rev m =
      diagonal (fun i => if i.val < r then S.M i i else 1) * pivotMatrix (revPivots m r) := by
    ext i j
    rw [diagonal_mul, diagonal_mul, pivotMatrix_apply _ hnodup]
    simp only [rev, of_apply, mem_revPivots]
    by_cases hi : i.val < r <;> simp [hi]
  have hRR : rev m * S.U * rev m * (rev m * S.U' * rev m) = 1 := by
    simp only [Matrix.mul_assoc]
    rw [rev_mul_rev_mul, ← Matrix.mul_assoc S.U, S.right, Matrix.one_mul, rev_mul_rev]
  have hRR' : rev m * S.U' * rev m * (rev m * S.U * rev m) = 1 := by
    simp only [Matrix.mul_assoc]
    rw [rev_mul_rev_mul, ← Matrix.mul_assoc S.U', S.right', Matrix.one_mul, rev_mul_rev]
  refine ⟨S.L, S.L', rev m * S.U * rev m, rev m * S.U' * rev m,
    fun i => if i.val < r then S.M i i else 1,
    fun i => if i.val < r then Ring.inverse (S.M i i) else 1,
    S.lower, S.lower', unitLower_rev_conj S.upper, unitLower_rev_conj S.upper',
    S.left, S.left', hRR, hRR', ?_, ?_⟩
  · intro i
    by_cases hi : i.val < r
    · simp only [hi, ↓reduceIte]
      exact Ring.mul_inverse_cancel _ (S.unit i hi)
    · simp only [hi, ↓reduceIte, mul_one]
  · have hPe : P * rev m = S.L * S.M * S.U * rev m := congrArg (fun X => X * rev m) S.eq
    have hsplit : S.L * S.M * S.U * rev m = S.L * (S.M * rev m) * (rev m * S.U * rev m) := by
      simp only [Matrix.mul_assoc]
      rw [rev_mul_rev_mul]
    have hSM : S.M * rev m =
        diagonal (fun i => if i.val < r then S.M i i else 1) * pivotMatrix (revPivots m r) :=
      (congrArg (fun X => X * rev m) hMdiag).trans hkey
    rw [hPe, hsplit, hSM]
    simp only [Matrix.mul_assoc]

/-- **A good move.** Let `P` be an idempotent that factors through `r` coordinates, with unit
leading principal minors of sizes `1..r`. Under incoming weights `α`, its reversed exchange is
the adapters `α L α⁻¹` and `R`, the shears by `K`, and one weighted reversed child on the first
`r` head coordinates and the last `r` tail coordinates, with weights `α δ`. -/
theorem good_move (P : Matrix (Fin m) (Fin m) R) (hidem : P * P = P) (r : ℕ) (hr : r ≤ m)
    (A : Matrix (Fin m) (Fin r) R) (B : Matrix (Fin r) (Fin m) R) (hP : P = A * B)
    (hminor : ∀ k (hk : k < r), IsUnit (lead (k + 1) (lt_of_lt_of_le hk hr) P).det)
    (α α' : Fin m → R) (hα : ∀ i, α i * α' i = 1) :
    ∃ (L L' R' R'' K : Matrix (Fin m) (Fin m) R) (δ δ' : Fin m → R),
      UnitLower L ∧ UnitLower L' ∧ UnitLower R' ∧ UnitLower R'' ∧ (∀ i, δ i * δ' i = 1) ∧
      ∀ s : State (Fin m) R,
        transform (diagonal α * L * diagonal α') R''
          (cross (-K) (Weighted.child r (fun i => α i * δ i) (fun i => α' i * δ' i)
            (cross K (transform (diagonal α * L' * diagonal α') R' s)))) =
          transform (diagonal α) 1
            (revExchangeOf (rev m) P (transform (diagonal α') 1 s)) := by
  obtain ⟨L, L', R', R'', δ, δ', hL, hL', hR, hR', hLL, hLL', hRR, hRR', hδ, hPC⟩ :=
    good_form P r hr A B hP hminor
  exact ⟨L, L', R', R'', _, δ, δ', hL, hL', hR, hR', hδ, fun s =>
    Weighted.weighted_good_child r α α' δ δ' hα hδ L L' R' R'' hLL hLL' hRR hRR' P hPC hidem s⟩

end IntegerMultBounds.MathlibTM2.Cover.GoodForm
