import IntegerMultBounds.Swap.Shear
import Mathlib.Tactic.Abel

/-! Lower triangular factorization (§4, Lemma 4.1): every matrix over a field
factors as `E₁ Π E₂` with `E₁`, `E₂` invertible lower triangular and `Π` a
partial permutation matrix. The elimination keeps finite sets of active rows
and columns. The topmost nonzero active row and its rightmost nonzero entry
give a pivot; a lower triangular column operation clears the pivot row to its
left, a lower triangular row operation clears the pivot column below, the pivot
is scaled to one and removed, and the elimination continues on the remaining
active indices. The identification of the number of pivots with the rank is a
separate statement. -/

namespace IntegerMultBounds.Swap.LowerTriangular

open Matrix Finset
open IntegerMultBounds.Swap.Shear (LowerTriangular pivotMatrix)

variable {F ι κ : Type*} [Field F] [Fintype ι] [Fintype κ] [LinearOrder ι] [LinearOrder κ]

/-- `M` agrees with the identity in every row and column outside `S`. -/
def IdOutside (S : Finset ι) (M : Matrix ι ι F) : Prop :=
  ∀ i j, (i ∉ S ∨ j ∉ S) → M i j = if i = j then 1 else 0

/-- `A` vanishes outside the active rows `S` and columns `T`. -/
def SupportedIn (S : Finset ι) (T : Finset κ) (A : Matrix ι κ F) : Prop :=
  ∀ i j, (i ∉ S ∨ j ∉ T) → A i j = 0

/-- A factorization `A = E₁ Π E₂` on the active rows `S` and columns `T`. The
factors are lower triangular with explicit two-sided inverses and act as the
identity outside the active indices; the pivots are active and form a partial
permutation. -/
structure Factorization (S : Finset ι) (T : Finset κ) (A : Matrix ι κ F) where
  E₁ : Matrix ι ι F
  E₁' : Matrix ι ι F
  E₂ : Matrix κ κ F
  E₂' : Matrix κ κ F
  L : List (ι × κ)
  lower₁ : LowerTriangular E₁
  lower₁' : LowerTriangular E₁'
  lower₂ : LowerTriangular E₂
  lower₂' : LowerTriangular E₂'
  inv₁ : E₁ * E₁' = 1
  inv₁' : E₁' * E₁ = 1
  inv₂ : E₂ * E₂' = 1
  inv₂' : E₂' * E₂ = 1
  id₁ : IdOutside S E₁
  id₂ : IdOutside T E₂
  mem : ∀ p ∈ L, p.1 ∈ S ∧ p.2 ∈ T
  nodup₁ : (L.map Prod.fst).Nodup
  nodup₂ : (L.map Prod.snd).Nodup
  eq : A = E₁ * pivotMatrix L * E₂

section Closure

omit [Fintype ι] in
theorem lower_one : LowerTriangular (1 : Matrix ι ι F) := fun _ _ h => one_apply_ne h.ne

omit [Fintype ι] in
theorem lower_add {M N : Matrix ι ι F} (hM : LowerTriangular M) (hN : LowerTriangular N) :
    LowerTriangular (M + N) := fun i j h => by rw [add_apply, hM i j h, hN i j h, add_zero]

omit [Fintype ι] in
theorem lower_sub {M N : Matrix ι ι F} (hM : LowerTriangular M) (hN : LowerTriangular N) :
    LowerTriangular (M - N) := fun i j h => by rw [sub_apply, hM i j h, hN i j h, sub_zero]

theorem lower_mul {M N : Matrix ι ι F} (hM : LowerTriangular M) (hN : LowerTriangular N) :
    LowerTriangular (M * N) := by
  intro i j hij
  rw [mul_apply]
  apply sum_eq_zero
  intro k _
  by_cases hik : i < k
  · rw [hM i k hik, zero_mul]
  · rw [hN k j (lt_of_le_of_lt (not_lt.mp hik) hij), mul_zero]

omit [Fintype ι] in
theorem lower_diagonal (d : ι → F) : LowerTriangular (diagonal d) :=
  fun _ _ h => diagonal_apply_ne d h.ne

omit [Fintype ι] in
theorem idOutside_one (S : Finset ι) : IdOutside S (1 : Matrix ι ι F) :=
  fun _ _ _ => one_apply

theorem idOutside_mul {S : Finset ι} {M N : Matrix ι ι F} (hM : IdOutside S M)
    (hN : IdOutside S N) : IdOutside S (M * N) := by
  intro i j hij
  rw [mul_apply]
  rcases hij with hi | hj
  · rw [sum_eq_single i]
    · rw [hM i i (Or.inl hi), ite_eq_left rfl, one_mul]
      exact hN i j (Or.inl hi)
    · intro k _ hk
      rw [hM i k (Or.inl hi), ite_eq_right (Ne.symm hk), zero_mul]
    · intro h
      exact absurd (mem_univ i) h
  · rw [sum_eq_single j]
    · rw [hN j j (Or.inr hj), ite_eq_left rfl, mul_one]
      exact hM i j (Or.inr hj)
    · intro k _ hk
      rw [hN k j (Or.inr hj), ite_eq_right hk, mul_zero]
    · intro h
      exact absurd (mem_univ j) h

omit [Fintype ι] in
theorem idOutside_mono {S S' : Finset ι} (h : S' ⊆ S) {M : Matrix ι ι F}
    (hM : IdOutside S' M) : IdOutside S M := by
  intro i j hij
  apply hM i j
  rcases hij with hi | hj
  · exact Or.inl fun h' => hi (h h')
  · exact Or.inr fun h' => hj (h h')

omit [Fintype ι] in
theorem idOutside_diagonal (S : Finset ι) (d : ι → F) (hd : ∀ i, i ∉ S → d i = 1) :
    IdOutside S (diagonal d) := by
  intro i j hij
  by_cases h : i = j
  · subst h
    rw [diagonal_apply_eq, ite_eq_left rfl]
    rcases hij with hi | hi <;> exact hd i hi
  · rw [diagonal_apply_ne d h, ite_eq_right h]

omit [Fintype ι] in
theorem idOutside_one_add {S : Finset ι} {N : Matrix ι ι F} (hN : SupportedIn S S N) :
    IdOutside S (1 + N) := by
  intro i j hij
  rw [add_apply, hN i j hij, add_zero, one_apply]

omit [Fintype ι] in
theorem idOutside_one_sub {S : Finset ι} {N : Matrix ι ι F} (hN : SupportedIn S S N) :
    IdOutside S (1 - N) := by
  intro i j hij
  rw [sub_apply, hN i j hij, sub_zero, one_apply]

/-- A square-zero perturbation of the identity has the opposite perturbation as
two-sided inverse. -/
theorem nilpotent_inv {N : Matrix ι ι F} (h : N * N = 0) :
    (1 + N) * (1 - N) = 1 ∧ (1 - N) * (1 + N) = 1 := by
  constructor
  · rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, h]
    abel
  · rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, h]
    abel

omit [Fintype κ] in
theorem idOutside_mul_single {S : Finset ι} {M : Matrix ι ι F} (hM : IdOutside S M) {r : ι}
    (hr : r ∉ S) (c : κ) : M * single r c (1 : F) = single r c 1 := by
  ext i j
  by_cases hj : j = c
  · subst hj
    rw [mul_apply, sum_eq_single r]
    · rw [hM i r (Or.inr hr)]
      by_cases hi : i = r
      · subst hi; simp [Matrix.single]
      · simp [Matrix.single, hi, Ne.symm hi]
    · intro k _ hk
      simp [Matrix.single, Ne.symm hk]
    · intro h
      exact absurd (mem_univ r) h
  · simp [Matrix.mul_apply, Matrix.single, Ne.symm hj]

omit [Fintype ι] in
theorem single_mul_idOutside {T : Finset κ} {N : Matrix κ κ F} (hN : IdOutside T N) {c : κ}
    (hc : c ∉ T) (r : ι) : single r c (1 : F) * N = single r c 1 := by
  ext i j
  by_cases hi : i = r
  · subst hi
    rw [mul_apply, sum_eq_single c]
    · rw [hN c j (Or.inl hc)]
      by_cases hj : j = c
      · subst hj; simp [Matrix.single]
      · simp [Matrix.single, Ne.symm hj]
    · intro k _ hk
      simp [Matrix.single, Ne.symm hk]
    · intro h
      exact absurd (mem_univ c) h
  · simp [Matrix.mul_apply, Matrix.single, Ne.symm hi]

end Closure

/-- The zero matrix factors trivially. -/
def trivialFactorization (S : Finset ι) (T : Finset κ) (A : Matrix ι κ F) (hA : A = 0) :
    Factorization S T A where
  E₁ := 1
  E₁' := 1
  E₂ := 1
  E₂' := 1
  L := []
  lower₁ := lower_one
  lower₁' := lower_one
  lower₂ := lower_one
  lower₂' := lower_one
  inv₁ := Matrix.one_mul 1
  inv₁' := Matrix.one_mul 1
  inv₂ := Matrix.one_mul 1
  inv₂' := Matrix.one_mul 1
  id₁ := idOutside_one S
  id₂ := idOutside_one T
  mem := by simp
  nodup₁ := List.nodup_nil
  nodup₂ := List.nodup_nil
  eq := by simp [pivotMatrix, hA]

section Step
variable (S : Finset ι) (T : Finset κ) (A : Matrix ι κ F) (r : ι) (c : κ)

/-- The pivot `(r, c)`: the topmost nonzero active row and its rightmost
nonzero entry. -/
structure IsPivot : Prop where
  supp : SupportedIn S T A
  mem_r : r ∈ S
  mem_c : c ∈ T
  rows : ∀ i, i < r → ∀ j, A i j = 0
  cols : ∀ j, c < j → A r j = 0
  ne : A r c ≠ 0

/-- Add multiples of column `c` to the earlier active columns. -/
def colOps : Matrix κ κ F :=
  of fun i j => if i = c ∧ j < c ∧ j ∈ T then -(A r j / A r c) else 0

def afterCols : Matrix ι κ F := A * (1 + colOps T A r c)

/-- Add multiples of row `r` to the later active rows. -/
def rowOps : Matrix ι ι F :=
  of fun i j => if j = r ∧ r < i ∧ i ∈ S then -(afterCols T A r c i c / A r c) else 0

def afterRows : Matrix ι κ F := (1 + rowOps S T A r c) * afterCols T A r c

/-- Scale row `r` by `a`. -/
def scaleRow (a : F) : Matrix ι ι F := diagonal fun i => if i = r then a else 1

def normalized : Matrix ι κ F := scaleRow r (A r c)⁻¹ * afterRows S T A r c

/-- The pivot row and column removed. -/
def residual : Matrix ι κ F := normalized S T A r c - single r c 1

omit [Fintype ι] [LinearOrder ι] in
theorem colOps_sq : colOps T A r c * colOps T A r c = 0 := by
  ext i j
  rw [mul_apply, zero_apply]
  apply sum_eq_zero
  intro k _
  simp only [colOps, of_apply]
  by_cases h1 : i = c ∧ k < c ∧ k ∈ T
  · by_cases h2 : k = c ∧ j < c ∧ j ∈ T
    · exact absurd h1.2.1 (by rw [h2.1]; exact lt_irrefl c)
    · rw [ite_eq_right h2, mul_zero]
  · rw [ite_eq_right h1, zero_mul]

omit [Fintype ι] [Fintype κ] [LinearOrder ι] in
theorem colOps_lower : LowerTriangular (colOps T A r c) := by
  intro i j hij
  simp only [colOps, of_apply]
  rw [ite_eq_right]
  rintro ⟨rfl, hj, _⟩
  exact lt_asymm hij hj

omit [Fintype ι] [Fintype κ] in
theorem colOps_supp (hp : IsPivot S T A r c) : SupportedIn T T (colOps T A r c) := by
  intro i j hij
  simp only [colOps, of_apply]
  rw [ite_eq_right]
  rintro ⟨rfl, _, hjT⟩
  rcases hij with hi | hj
  · exact hi hp.mem_c
  · exact hj hjT

omit [Fintype ι] [LinearOrder ι] in
theorem afterCols_apply (i : ι) (j : κ) :
    afterCols T A r c i j = A i j + A i c * (if j < c ∧ j ∈ T then -(A r j / A r c) else 0) := by
  unfold afterCols
  rw [Matrix.mul_add, Matrix.mul_one, add_apply, mul_apply, sum_eq_single c]
  · simp [colOps]
  · intro k _ hk
    simp [colOps, hk]
  · intro h
    exact absurd (mem_univ c) h

omit [Fintype ι] in
theorem afterCols_row (hp : IsPivot S T A r c) (j : κ) :
    afterCols T A r c r j = if j = c then A r c else 0 := by
  rw [afterCols_apply]
  by_cases hj : j = c
  · subst hj
    simp
  · rw [ite_eq_right hj]
    by_cases hjc : j < c
    · by_cases hjT : j ∈ T
      · rw [ite_eq_left ⟨hjc, hjT⟩, mul_neg, mul_div_cancel₀ _ hp.ne, add_neg_cancel]
      · rw [ite_eq_right (fun h => hjT h.2), mul_zero, add_zero]
        exact hp.supp r j (Or.inr hjT)
    · rw [ite_eq_right (fun h => hjc h.1), mul_zero, add_zero]
      exact hp.cols j (lt_of_le_of_ne (not_lt.mp hjc) (Ne.symm hj))

omit [Fintype ι] [LinearOrder ι] in
theorem afterCols_col (i : ι) : afterCols T A r c i c = A i c := by
  rw [afterCols_apply, ite_eq_right (fun h => lt_irrefl c h.1), mul_zero, add_zero]

omit [Fintype ι] in
theorem afterCols_rows (hp : IsPivot S T A r c) (i : ι) (hi : i < r) (j : κ) :
    afterCols T A r c i j = 0 := by
  rw [afterCols_apply, hp.rows i hi j, hp.rows i hi c, zero_mul, add_zero]

omit [Fintype ι] in
theorem afterCols_supp (hp : IsPivot S T A r c) : SupportedIn S T (afterCols T A r c) := by
  intro i j hij
  rw [afterCols_apply]
  rcases hij with hi | hj
  · rw [hp.supp i j (Or.inl hi), hp.supp i c (Or.inl hi), zero_mul, add_zero]
  · rw [hp.supp i j (Or.inr hj), ite_eq_right (fun h => hj h.2), mul_zero, add_zero]

theorem rowOps_sq : rowOps S T A r c * rowOps S T A r c = 0 := by
  ext i j
  rw [mul_apply, zero_apply]
  apply sum_eq_zero
  intro k _
  simp only [rowOps, of_apply]
  by_cases h1 : k = r ∧ r < i ∧ i ∈ S
  · by_cases h2 : j = r ∧ r < k ∧ k ∈ S
    · exact absurd h2.2.1 (by rw [h1.1]; exact lt_irrefl r)
    · rw [ite_eq_right h2, mul_zero]
  · rw [ite_eq_right h1, zero_mul]

omit [Fintype ι] in
theorem rowOps_lower : LowerTriangular (rowOps S T A r c) := by
  intro i j hij
  simp only [rowOps, of_apply]
  rw [ite_eq_right]
  rintro ⟨rfl, hi, _⟩
  exact lt_asymm hij hi

omit [Fintype ι] in
theorem rowOps_supp (hp : IsPivot S T A r c) : SupportedIn S S (rowOps S T A r c) := by
  intro i j hij
  simp only [rowOps, of_apply]
  rw [ite_eq_right]
  rintro ⟨rfl, _, hiS⟩
  rcases hij with hi | hj
  · exact hi hiS
  · exact hj hp.mem_r

theorem afterRows_apply (i : ι) (j : κ) :
    afterRows S T A r c i j = afterCols T A r c i j +
      (if r < i ∧ i ∈ S then -(afterCols T A r c i c / A r c) else 0) * afterCols T A r c r j := by
  unfold afterRows
  rw [Matrix.add_mul, Matrix.one_mul, add_apply, mul_apply, sum_eq_single r]
  · simp [rowOps]
  · intro k _ hk
    simp [rowOps, hk]
  · intro h
    exact absurd (mem_univ r) h

theorem afterRows_row (hp : IsPivot S T A r c) (j : κ) :
    afterRows S T A r c r j = if j = c then A r c else 0 := by
  rw [afterRows_apply, ite_eq_right (fun h => lt_irrefl r h.1), zero_mul, add_zero]
  exact afterCols_row S T A r c hp j

theorem afterRows_col (hp : IsPivot S T A r c) (i : ι) :
    afterRows S T A r c i c = if i = r then A r c else 0 := by
  rw [afterRows_apply, afterCols_col T A r c i, afterCols_col T A r c r]
  by_cases hi : i = r
  · subst hi
    rw [ite_eq_left rfl, ite_eq_right (fun h => lt_irrefl _ h.1), zero_mul, add_zero]
  · rw [ite_eq_right hi]
    by_cases hri : r < i
    · by_cases hiS : i ∈ S
      · rw [ite_eq_left ⟨hri, hiS⟩, neg_mul, div_mul_cancel₀ _ hp.ne, add_neg_cancel]
      · rw [ite_eq_right (fun h => hiS h.2), zero_mul, add_zero]
        exact hp.supp i c (Or.inl hiS)
    · rw [ite_eq_right (fun h => hri h.1), zero_mul, add_zero]
      exact hp.rows i (lt_of_le_of_ne (not_lt.mp hri) hi) c

theorem afterRows_supp (hp : IsPivot S T A r c) : SupportedIn S T (afterRows S T A r c) := by
  intro i j hij
  rw [afterRows_apply]
  rcases hij with hi | hj
  · rw [afterCols_supp S T A r c hp i j (Or.inl hi), ite_eq_right (fun h => hi h.2), zero_mul, add_zero]
  · rw [afterCols_supp S T A r c hp i j (Or.inr hj), afterCols_supp S T A r c hp r j (Or.inr hj),
      mul_zero, add_zero]

theorem normalized_apply (i : ι) (j : κ) :
    normalized S T A r c i j = (if i = r then (A r c)⁻¹ else 1) * afterRows S T A r c i j := by
  unfold normalized scaleRow
  rw [diagonal_mul]

theorem normalized_row (hp : IsPivot S T A r c) (j : κ) :
    normalized S T A r c r j = if j = c then 1 else 0 := by
  rw [normalized_apply, ite_eq_left rfl, afterRows_row S T A r c hp]
  by_cases hj : j = c
  · rw [ite_eq_left hj, ite_eq_left hj, inv_mul_cancel₀ hp.ne]
  · rw [ite_eq_right hj, ite_eq_right hj, mul_zero]

theorem normalized_col (hp : IsPivot S T A r c) (i : ι) :
    normalized S T A r c i c = if i = r then 1 else 0 := by
  rw [normalized_apply, afterRows_col S T A r c hp]
  by_cases hi : i = r
  · rw [ite_eq_left hi, ite_eq_left hi, ite_eq_left hi, inv_mul_cancel₀ hp.ne]
  · rw [ite_eq_right hi, ite_eq_right hi, ite_eq_right hi, mul_zero]

theorem normalized_supp (hp : IsPivot S T A r c) : SupportedIn S T (normalized S T A r c) := by
  intro i j hij
  rw [normalized_apply, afterRows_supp S T A r c hp i j hij, mul_zero]

theorem residual_supp (hp : IsPivot S T A r c) :
    SupportedIn (S.erase r) (T.erase c) (residual S T A r c) := by
  intro i j hij
  unfold residual
  rw [sub_apply]
  rcases hij with hi | hj
  · rw [Finset.mem_erase, not_and_or, not_not] at hi
    rcases hi with hi | hi
    · rw [hi, normalized_row S T A r c hp]
      by_cases hj : j = c
      · rw [hj]; simp
      · simp [Matrix.single, hj, Ne.symm hj]
    · have hri : r ≠ i := fun h => hi (h ▸ hp.mem_r)
      rw [normalized_supp S T A r c hp i j (Or.inl hi)]
      simp [Matrix.single, hri]
  · rw [Finset.mem_erase, not_and_or, not_not] at hj
    rcases hj with hj | hj
    · rw [hj, normalized_col S T A r c hp]
      by_cases hi : i = r
      · rw [hi]; simp
      · simp [Matrix.single, hi, Ne.symm hi]
    · have hcj : c ≠ j := fun h => hj (h ▸ hp.mem_c)
      rw [normalized_supp S T A r c hp i j (Or.inr hj)]
      simp [Matrix.single, hcj]

theorem scaleRow_mul_inv (a : F) (ha : a ≠ 0) :
    scaleRow r a * scaleRow r a⁻¹ = (1 : Matrix ι ι F) := by
  unfold scaleRow
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  by_cases hi : i = r
  · rw [ite_eq_left hi, ite_eq_left hi, mul_inv_cancel₀ ha]
  · rw [ite_eq_right hi, ite_eq_right hi, mul_one]

theorem scaleRow_inv_mul (a : F) (ha : a ≠ 0) :
    scaleRow r a⁻¹ * scaleRow r a = (1 : Matrix ι ι F) := by
  unfold scaleRow
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  by_cases hi : i = r
  · rw [ite_eq_left hi, ite_eq_left hi, inv_mul_cancel₀ ha]
  · rw [ite_eq_right hi, ite_eq_right hi, mul_one]

/-- Undo the row scaling, the row operations, and the column operations. -/
theorem reconstruct (hp : IsPivot S T A r c) :
    (1 - rowOps S T A r c) * scaleRow r (A r c) * normalized S T A r c *
      (1 - colOps T A r c) = A := by
  have hM := (nilpotent_inv (rowOps_sq S T A r c)).2
  have hN := (nilpotent_inv (colOps_sq T A r c)).1
  unfold normalized afterRows afterCols
  simp only [Matrix.mul_assoc]
  rw [hN, Matrix.mul_one, ← Matrix.mul_assoc (scaleRow r (A r c)), scaleRow_mul_inv r _ hp.ne,
    Matrix.one_mul, ← Matrix.mul_assoc (1 - rowOps S T A r c), hM, Matrix.one_mul]

theorem normalized_eq (f : Factorization (S.erase r) (T.erase c) (residual S T A r c)) :
    normalized S T A r c = f.E₁ * pivotMatrix ((r, c) :: f.L) * f.E₂ := by
  have h1 : f.E₁ * single r c (1 : F) * f.E₂ = single r c 1 := by
    rw [idOutside_mul_single f.id₁ (Finset.notMem_erase r S),
      single_mul_idOutside f.id₂ (Finset.notMem_erase c T)]
  have h2 := f.eq
  unfold residual at h2
  rw [pivotMatrix, Matrix.mul_add, Matrix.add_mul, h1, ← h2]
  abel

/-- One elimination step: a pivot and a factorization of the residual give a
factorization on the full active sets. -/
def step (hp : IsPivot S T A r c)
    (f : Factorization (S.erase r) (T.erase c) (residual S T A r c)) :
    Factorization S T A where
  E₁ := (1 - rowOps S T A r c) * scaleRow r (A r c) * f.E₁
  E₁' := f.E₁' * scaleRow r (A r c)⁻¹ * (1 + rowOps S T A r c)
  E₂ := f.E₂ * (1 - colOps T A r c)
  E₂' := (1 + colOps T A r c) * f.E₂'
  L := (r, c) :: f.L
  lower₁ := lower_mul (lower_mul (lower_sub lower_one (rowOps_lower S T A r c))
    (lower_diagonal _)) f.lower₁
  lower₁' := lower_mul (lower_mul f.lower₁' (lower_diagonal _))
    (lower_add lower_one (rowOps_lower S T A r c))
  lower₂ := lower_mul f.lower₂ (lower_sub lower_one (colOps_lower T A r c))
  lower₂' := lower_mul (lower_add lower_one (colOps_lower T A r c)) f.lower₂'
  inv₁ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc f.E₁, f.inv₁, Matrix.one_mul,
      ← Matrix.mul_assoc (scaleRow r (A r c)), scaleRow_mul_inv r _ hp.ne, Matrix.one_mul,
      (nilpotent_inv (rowOps_sq S T A r c)).2]
  inv₁' := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (1 + rowOps S T A r c), (nilpotent_inv (rowOps_sq S T A r c)).1,
      Matrix.one_mul, ← Matrix.mul_assoc (scaleRow r (A r c)⁻¹), scaleRow_inv_mul r _ hp.ne,
      Matrix.one_mul, f.inv₁']
  inv₂ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (1 - colOps T A r c), (nilpotent_inv (colOps_sq T A r c)).2,
      Matrix.one_mul, f.inv₂]
  inv₂' := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc f.E₂', f.inv₂', Matrix.one_mul,
      (nilpotent_inv (colOps_sq T A r c)).1]
  id₁ := idOutside_mul (idOutside_mul (idOutside_one_sub (rowOps_supp S T A r c hp))
    (idOutside_diagonal S _ fun i hi => ite_eq_right (fun h : i = r => hi (h ▸ hp.mem_r))))
    (idOutside_mono (erase_subset r S) f.id₁)
  id₂ := idOutside_mul (idOutside_mono (erase_subset c T) f.id₂)
    (idOutside_one_sub (colOps_supp S T A r c hp))
  mem := by
    intro p hp'
    rcases List.mem_cons.mp hp' with rfl | h
    · exact ⟨hp.mem_r, hp.mem_c⟩
    · obtain ⟨h1, h2⟩ := f.mem p h
      exact ⟨mem_of_mem_erase h1, mem_of_mem_erase h2⟩
  nodup₁ := by
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, f.nodup₁⟩
    intro h
    obtain ⟨p, hp', hpr⟩ := List.mem_map.mp h
    exact ne_of_mem_erase (f.mem p hp').1 hpr
  nodup₂ := by
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, f.nodup₂⟩
    intro h
    obtain ⟨p, hp', hpc⟩ := List.mem_map.mp h
    exact ne_of_mem_erase (f.mem p hp').2 hpc
  eq := by
    refine (reconstruct S T A r c hp).symm.trans ?_
    rw [normalized_eq S T A r c f]
    simp only [Matrix.mul_assoc]

end Step

/-- Elimination on the active rows and columns terminates with a factorization. -/
theorem exists_factorization : ∀ (n : ℕ) (S : Finset ι) (T : Finset κ) (A : Matrix ι κ F),
    S.card + T.card = n → SupportedIn S T A → Nonempty (Factorization S T A) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S T A hn hA
  classical
  by_cases h0 : A = 0
  · exact ⟨trivialFactorization S T A h0⟩
  have hex : ∃ i j, A i j ≠ 0 := by
    by_contra h
    push Not at h
    exact h0 (Matrix.ext fun i j => by rw [h i j, zero_apply])
  set R := univ.filter (fun i => ∃ j, A i j ≠ 0) with hRdef
  have hR : R.Nonempty := by
    obtain ⟨i, j, h⟩ := hex
    exact ⟨i, by simp only [hRdef, mem_filter, mem_univ, true_and]; exact ⟨j, h⟩⟩
  set r := R.min' hR with hrdef
  have hrR : r ∈ R := R.min'_mem hR
  obtain ⟨j₀, hj₀⟩ : ∃ j, A r j ≠ 0 := by
    simpa only [hRdef, mem_filter, mem_univ, true_and] using hrR
  set C := univ.filter (fun j => A r j ≠ 0) with hCdef
  have hC : C.Nonempty := ⟨j₀, by simp only [hCdef, mem_filter, mem_univ, true_and]; exact hj₀⟩
  set c := C.max' hC with hcdef
  have hc : A r c ≠ 0 := by
    have := C.max'_mem hC
    simpa only [hCdef, mem_filter, mem_univ, true_and] using this
  have hp : IsPivot S T A r c :=
    { supp := hA
      mem_r := by
        by_contra h
        exact hc (hA r c (Or.inl h))
      mem_c := by
        by_contra h
        exact hc (hA r c (Or.inr h))
      rows := by
        intro i hi j
        by_contra h
        have hiR : i ∈ R := by
          simp only [hRdef, mem_filter, mem_univ, true_and]
          exact ⟨j, h⟩
        exact absurd (R.min'_le i hiR) (not_le.mpr hi)
      cols := by
        intro j hj
        by_contra h
        have hjC : j ∈ C := by
          simp only [hCdef, mem_filter, mem_univ, true_and]
          exact h
        exact absurd (C.le_max' j hjC) (not_le.mpr hj)
      ne := hc }
  have hcard : (S.erase r).card + (T.erase c).card < n := by
    rw [card_erase_of_mem hp.mem_r, card_erase_of_mem hp.mem_c]
    have h1 := card_pos.mpr ⟨r, hp.mem_r⟩
    have h2 := card_pos.mpr ⟨c, hp.mem_c⟩
    omega
  obtain ⟨f⟩ := ih _ hcard (S.erase r) (T.erase c) (residual S T A r c) rfl
    (residual_supp S T A r c hp)
  exact ⟨step S T A r c hp f⟩

/-- Lemma 4.1: every matrix over a field is `E₁ Π E₂` with `E₁`, `E₂` lower
triangular with lower triangular inverses and `Π` a partial permutation matrix. -/
theorem factorization (A : Matrix ι κ F) : Nonempty (Factorization univ univ A) :=
  exists_factorization _ univ univ A rfl fun _ _ h => by
    rcases h with h | h <;> exact absurd (mem_univ _) h

end IntegerMultBounds.Swap.LowerTriangular
