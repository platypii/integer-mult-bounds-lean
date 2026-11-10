module

public import IntegerMultBounds.MathlibTM2.Cover.GoodForm
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Unit-pivot elimination over a local ring

On a bad cover class some leading minor of the projector is not a unit, and the good normal form
does not apply. The fallback eliminates the whole residual, an invertible matrix over the atom
ring `Z/q^w`, choosing a unit pivot in every column. A local ring always has one: if every
candidate in a column were a non-unit, the determinant would lie in the maximal ideal
(`exists_unit`).

`fallback_form`: for an invertible `n × n` matrix `G` over a local ring there is a product `E` of
exactly `n (n - 1)` row additions and `n` row exchanges with `E G` diagonal with unit entries
(`Elim` counts both). Additions with coefficient zero and exchanges of a row with itself are
kept, so the schedule has the same shape for every matrix.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.Fallback

open Matrix
open IntegerMultBounds.MathlibTM2.Cover.GoodForm (colMat colMat_mul colMat_mul_colMat add_mul_sub)

variable {n : ℕ} {R : Type*} [CommRing R]

/-- The exchange of rows `i` and `j`. -/
def swapMat (i j : Fin n) : Matrix (Fin n) (Fin n) R :=
  of fun a b => if b = Equiv.swap i j a then 1 else 0

theorem swapMat_mul (i j : Fin n) (M : Matrix (Fin n) (Fin n) R) (a b : Fin n) :
    ((swapMat i j : Matrix (Fin n) (Fin n) R) * M) a b = M (Equiv.swap i j a) b := by
  rw [mul_apply, Finset.sum_eq_single (Equiv.swap i j a)]
  · simp [swapMat]
  · intro l _ hl
    simp [swapMat, hl]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem swapMat_mul_self (i j : Fin n) :
    (swapMat i j : Matrix (Fin n) (Fin n) R) * swapMat i j = 1 := by
  ext a b
  rw [swapMat_mul]
  simp only [swapMat, of_apply, Equiv.swap_apply_self, one_apply]
  by_cases h : a = b
  · subst h
    simp
  · have h' : ¬b = a := fun e => h e.symm
    simp [h, h']

/-- Products of `a` row additions and `s` row exchanges. The addition
`1 + colMat k (Pi.single i c)` adds `c` times row `k` to row `i`. -/
inductive Elim : ℕ → ℕ → Matrix (Fin n) (Fin n) R → Prop
  | one : Elim 0 0 1
  | add {a s : ℕ} {E : Matrix (Fin n) (Fin n) R} (i k : Fin n) (c : R) (hik : i ≠ k) :
      Elim a s E → Elim (a + 1) s ((1 + colMat k (Pi.single i c)) * E)
  | swap {a s : ℕ} {E : Matrix (Fin n) (Fin n) R} (i j : Fin n) :
      Elim a s E → Elim a (s + 1) (swapMat i j * E)

theorem Elim.mul {a s a' s' : ℕ} {E E' : Matrix (Fin n) (Fin n) R} (h : Elim a s E)
    (h' : Elim a' s' E') : Elim (a + a') (s + s') (E * E') := by
  induction h with
  | one =>
    rw [Nat.zero_add, Nat.zero_add, Matrix.one_mul]
    exact h'
  | add i k c hik _ ih =>
    rw [Matrix.mul_assoc, Nat.add_right_comm]
    exact Elim.add i k c hik ih
  | swap i j _ ih =>
    rw [Matrix.mul_assoc, Nat.add_right_comm]
    exact Elim.swap i j ih

theorem Elim.inv {a s : ℕ} {E : Matrix (Fin n) (Fin n) R} (h : Elim a s E) :
    ∃ E' : Matrix (Fin n) (Fin n) R, E' * E = 1 := by
  induction h with
  | one => exact ⟨1, Matrix.one_mul 1⟩
  | add i k c hik _ ih =>
    obtain ⟨E', hE⟩ := ih
    have hinv := (add_mul_sub (colMat_mul_colMat k (Pi.single i c) (Pi.single i c)
      (by simp [hik.symm]))).2
    exact ⟨E' * (1 - colMat k (Pi.single i c)), by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 - colMat k (Pi.single i c)), hinv,
        Matrix.one_mul, hE]⟩
  | swap i j _ ih =>
    obtain ⟨E', hE⟩ := ih
    exact ⟨E' * swapMat i j, by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (swapMat i j), swapMat_mul_self, Matrix.one_mul,
        hE]⟩

theorem Elim.isUnit_det {a s : ℕ} {E : Matrix (Fin n) (Fin n) R} (h : Elim a s E) :
    IsUnit E.det := by
  obtain ⟨E', hE⟩ := h.inv
  have hd := congrArg det hE
  rw [det_mul, det_one] at hd
  exact isUnit_iff_exists_inv'.mpr ⟨_, hd⟩

/-- Clearing a column: subtracting multiples of row `k` from the rows of `T`. -/
theorem elim_col (k : Fin n) (c : Fin n → R) (T : Finset (Fin n)) (hT : k ∉ T) :
    Elim T.card 0 (1 - colMat k fun i => if i ∈ T then c i else 0) := by
  induction T using Finset.induction_on with
  | empty =>
    have h0 : colMat k (fun i => if i ∈ (∅ : Finset (Fin n)) then c i else 0) = 0 := by
      ext a b
      simp [colMat]
    rw [h0, sub_zero]
    exact Elim.one
  | insert i T hi ih =>
    have hk : k ∉ T := fun h => hT (Finset.mem_insert_of_mem h)
    have hik : i ≠ k := fun h => hT (by rw [← h]; exact Finset.mem_insert_self i T)
    have hN : colMat k (Pi.single i (-c i)) * colMat k (fun l => if l ∈ T then c l else 0) = 0 :=
      colMat_mul_colMat k _ _ (by simp [hk])
    have hsum : colMat k (fun l => if l ∈ insert i T then c l else 0) =
        colMat k (fun l => if l ∈ T then c l else 0) - colMat k (Pi.single i (-c i)) := by
      ext a b
      by_cases hb : b = k
      · by_cases ha : a = i
        · simp [colMat, hb, ha, hi]
        · simp [colMat, hb, ha, Finset.mem_insert, Pi.single_apply]
      · simp [colMat, hb]
    have hprod : (1 + colMat k (Pi.single i (-c i))) *
        (1 - colMat k fun l => if l ∈ T then c l else 0) =
        1 - colMat k fun l => if l ∈ insert i T then c l else 0 := by
      have h (N M : Matrix (Fin n) (Fin n) R) : (1 + N) * (1 - M) = 1 - (M - N) - N * M := by
        noncomm_ring
      rw [hsum, h, hN, sub_zero]
    rw [← hprod, Finset.card_insert_of_notMem hi]
    exact Elim.add i k _ hik (ih hk)

/-- Columns before `k` are diagonal. -/
def ColCleared (k : ℕ) (M : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j : Fin n, j.val < k → i ≠ j → M i j = 0

/-- A local ring has a unit pivot in the next column, at or below the diagonal. -/
theorem exists_unit [IsLocalRing R] {M : Matrix (Fin n) (Fin n) R} {k : ℕ} (hk : k < n)
    (hM : ColCleared k M) (hdet : IsUnit M.det) :
    ∃ i : Fin n, k ≤ i.val ∧ IsUnit (M i ⟨k, hk⟩) := by
  by_contra hno
  push Not at hno
  have hsum : M.det = ∑ i, adjugate M ⟨k, hk⟩ i * M i ⟨k, hk⟩ := by
    have h := congrFun (congrFun (adjugate_mul M) ⟨k, hk⟩) ⟨k, hk⟩
    rw [mul_apply, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one] at h
    exact h.symm
  have hmem : M.det ∈ IsLocalRing.maximalIdeal R := by
    rw [hsum]
    refine sum_mem fun i _ => ?_
    by_cases hi : k ≤ i.val
    · exact Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).mpr (hno i hi))
    · have hz : adjugate M ⟨k, hk⟩ i = 0 := by
        rw [adjugate_apply]
        refine det_eq_zero_of_column_eq_zero i fun l => ?_
        by_cases hl : l = i
        · rw [hl, updateRow_self,
            Pi.single_eq_of_ne fun h => hi (by rw [h])]
        · rw [updateRow_ne hl]
          exact hM l i (not_le.mp hi) hl
      rw [hz, zero_mul]
      exact Ideal.zero_mem _
  exact (IsLocalRing.mem_maximalIdeal _).mp hmem hdet

/-- The operation of one column with pivot row `i₀`: exchange rows `K` and `i₀`, then subtract
multiples of row `K` from every other row. `p'` is the inverse of the pivot. -/
def stepOp (K i₀ : Fin n) (M : Matrix (Fin n) (Fin n) R) (p' : R) : Matrix (Fin n) (Fin n) R :=
  (1 - colMat K fun i => if i ∈ Finset.univ.erase K then M (Equiv.swap K i₀ i) K * p' else 0) *
    swapMat K i₀

/-- One column: exchange the pivot row into place, then clear the column. -/
theorem step (K i₀ : Fin n) (hKi : K.val ≤ i₀.val) (M : Matrix (Fin n) (Fin n) R)
    (hM : ColCleared K.val M) (p' : R) (hpp : M i₀ K * p' = 1) :
    Elim (n - 1) 1 (stepOp K i₀ M p') ∧ ColCleared (K.val + 1) (stepOp K i₀ M p' * M) ∧
      (∀ j : Fin n, j.val < K.val → (stepOp K i₀ M p' * M) j j = M j j) ∧
      (stepOp K i₀ M p' * M) K K = M i₀ K := by
  have hent (a b : Fin n) :
      (stepOp K i₀ M p' * M) a b =
      M (Equiv.swap K i₀ a) b -
        (if a ∈ Finset.univ.erase K then M (Equiv.swap K i₀ a) K * p' else 0) * M i₀ b := by
    rw [stepOp, Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, colMat_mul,
      swapMat_mul, swapMat_mul, Equiv.swap_apply_left]
  have hfix (b : Fin n) (hb : b.val < K.val) : Equiv.swap K i₀ b = b :=
    Equiv.swap_apply_of_ne_of_ne (fun h => by rw [h] at hb; omega)
      (fun h => by rw [h] at hb; omega)
  have hrow (b : Fin n) (hb : b.val < K.val) : M i₀ b = 0 :=
    hM i₀ b hb fun h => by rw [h] at hKi; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := (elim_col K (fun i => M (Equiv.swap K i₀ i) K * p') (Finset.univ.erase K)
      (Finset.notMem_erase K _)).mul (Elim.swap K i₀ Elim.one)
    rw [Nat.add_zero, Nat.zero_add, Nat.zero_add, Matrix.mul_one,
      Finset.card_erase_of_mem (Finset.mem_univ K), Finset.card_univ, Fintype.card_fin] at h
    exact h
  · intro a b hb hab
    rw [hent]
    by_cases hbK : b.val < K.val
    · have hne : Equiv.swap K i₀ a ≠ b := fun h => hab (by
        have h2 := congrArg (Equiv.swap K i₀) h
        rw [Equiv.swap_apply_self, hfix b hbK] at h2
        exact h2)
      rw [hM _ b hbK hne, hrow b hbK, mul_zero, sub_zero]
    · have hbe : b = K := Fin.ext (by omega)
      have haK : a ∈ Finset.univ.erase K :=
        Finset.mem_erase.mpr ⟨fun h => hab (h.trans hbe.symm), Finset.mem_univ _⟩
      rw [hbe, ite_eq_left haK]
      linear_combination (-(M (Equiv.swap K i₀ a) K)) * hpp
  · intro j hj
    rw [hent, hfix j hj, hrow j hj, mul_zero, sub_zero]
  · rw [hent, ite_eq_right (Finset.notMem_erase K _), zero_mul, sub_zero, Equiv.swap_apply_left]

/-- Elimination of the first `k` columns. -/
theorem stage [IsLocalRing R] (G : Matrix (Fin n) (Fin n) R) (hG : IsUnit G.det) :
    ∀ k, k ≤ n → ∃ E M : Matrix (Fin n) (Fin n) R, Elim (k * (n - 1)) k E ∧ E * G = M ∧
      ColCleared k M ∧ ∀ j : Fin n, j.val < k → IsUnit (M j j) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨1, G, by rw [Nat.zero_mul]; exact Elim.one, Matrix.one_mul G,
      fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk
    obtain ⟨E, M, hE, hEG, hM, hu⟩ := ih (by omega)
    have hkn : k < n := hk
    have hdet : IsUnit M.det := by
      rw [← hEG, det_mul]
      exact hE.isUnit_det.mul hG
    obtain ⟨i₀, hi₀, hp⟩ := exists_unit hkn hM hdet
    obtain ⟨p', hpp⟩ := hp.exists_right_inv
    obtain ⟨hF, hcl, hdiag, hKK⟩ := step ⟨k, hkn⟩ i₀ hi₀ M hM p' hpp
    refine ⟨stepOp ⟨k, hkn⟩ i₀ M p' * E, stepOp ⟨k, hkn⟩ i₀ M p' * M, ?_,
      by rw [Matrix.mul_assoc, hEG], hcl, fun j hj => ?_⟩
    · have h := hF.mul hE
      have e : n - 1 + k * (n - 1) = (k + 1) * (n - 1) := by ring
      rw [e, Nat.add_comm 1 k] at h
      exact h
    · by_cases hjk : j.val < k
      · rw [hdiag j hjk]
        exact hu j hjk
      · have hj' : j = ⟨k, hkn⟩ := Fin.ext (show j.val = k by omega)
        rw [hj', hKK]
        exact hp

/-- **The fallback normal form.** An invertible matrix over a local ring becomes diagonal with
unit entries after `n (n - 1)` row additions and `n` row exchanges. -/
theorem fallback_form [IsLocalRing R] (G : Matrix (Fin n) (Fin n) R) (hG : IsUnit G.det) :
    ∃ (E : Matrix (Fin n) (Fin n) R) (d : Fin n → R),
      Elim (n * (n - 1)) n E ∧ E * G = diagonal d ∧ ∀ i, IsUnit (d i) := by
  obtain ⟨E, M, hE, hEG, hM, hu⟩ := stage G hG n le_rfl
  refine ⟨E, fun i => M i i, hE, ?_, fun i => hu i i.isLt⟩
  rw [hEG]
  ext i j
  by_cases hij : i = j
  · rw [hij, diagonal_apply_eq]
  · rw [diagonal_apply_ne _ hij]
    exact hM i j j.isLt hij

/-! ### From row operations to children -/

theorem mul_swapMat (i j : Fin n) (M : Matrix (Fin n) (Fin n) R) (a b : Fin n) :
    (M * (swapMat i j : Matrix (Fin n) (Fin n) R)) a b = M a (Equiv.swap i j b) := by
  rw [mul_apply, Finset.sum_eq_single (Equiv.swap i j b)]
  · simp [swapMat]
  · intro l _ hl
    have hne : ¬b = Equiv.swap i j l := fun h => hl (by rw [h, Equiv.swap_apply_self])
    simp [swapMat, hne]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- An addition to row `i` from row `k` is the addition to row `k` from row `i` between two
exchanges of the two rows. When `i` precedes `k` in the address order, the inner addition has a
later target and is an ordered pass; the two exchanges are children. -/
theorem add_conj (i k : Fin n) (c : R) :
    (swapMat i k : Matrix (Fin n) (Fin n) R) * (1 + colMat i (Pi.single k c)) * swapMat i k =
      1 + colMat k (Pi.single i c) := by
  ext a b
  have h1 : Equiv.swap i k b = i ↔ b = k := by
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
  have h2 : Equiv.swap i k a = k ↔ a = i := by
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
  rw [mul_swapMat, swapMat_mul]
  simp only [Matrix.add_apply, colMat, of_apply, one_apply, Pi.single_apply,
    Equiv.apply_eq_iff_eq, h1, h2]

/-- An ordinary weighted exchange of two fields is a weighted reversed exchange between two
reversals of the later field: `(h, d) ↦ (A d, A⁻¹ h)`. -/
theorem ordinary_of_reversed {ι : Type*} [Fintype ι] [DecidableEq ι] (C A A' : Matrix ι ι R)
    (hC : C * C = 1) (s : IntegerMultBounds.Swap.Shear.State ι R) :
    M8.Exchange.transform 1 C (Weighted.weighted C A A' (M8.Exchange.transform 1 C s)) =
      (A *ᵥ s.2, A' *ᵥ s.1) := by
  have hCC (X : Matrix ι ι R) : C * (C * X) = X := by rw [← Matrix.mul_assoc, hC, Matrix.one_mul]
  simp only [Weighted.weighted, M8.Exchange.transform, one_mulVec, mulVec_mulVec, hC, hCC,
    Matrix.one_mul]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
