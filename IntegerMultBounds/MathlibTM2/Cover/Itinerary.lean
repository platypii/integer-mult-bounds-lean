module

public import IntegerMultBounds.MathlibTM2.Cover.Fallback

/-!
# The pivot itinerary depends only on the residue class

The fallback runs one schedule on a whole packet of labels that share their low digits, so the
pivot rows must be the same for every lift of one residue class.

* `run p G k`: the matrix after `k` columns of unit-pivot elimination with the pivot rows `p`.
* `Valid p G k`: each of the first `k` pivots lies at or below the diagonal and is a unit.
* `itinerary_form`: a valid itinerary makes `G` diagonal with unit entries after `n (n - 1)` row
  additions and `n` row exchanges.
* `exists_itinerary`: an invertible matrix over a local ring has a valid itinerary.
* `valid_congr`: for a ring homomorphism that reflects units, such as `Z/q^w → F_q`, validity of
  an itinerary depends only on the image of `G`. The elimination commutes with the homomorphism
  (`run_map`), and a pivot is a unit exactly when its image is.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.Itinerary

open Matrix
open IntegerMultBounds.MathlibTM2.Cover.GoodForm (colMat)
open IntegerMultBounds.MathlibTM2.Cover.Fallback
  (swapMat Elim ColCleared stepOp step exists_unit)

variable {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]

/-- The matrix after `k` columns of elimination with the pivot rows `p`. -/
noncomputable def run (p : Fin n → Fin n) (G : Matrix (Fin n) (Fin n) R) :
    ℕ → Matrix (Fin n) (Fin n) R
  | 0 => G
  | k + 1 =>
    if h : k < n then
      stepOp ⟨k, h⟩ (p ⟨k, h⟩) (run p G k) (Ring.inverse (run p G k (p ⟨k, h⟩) ⟨k, h⟩)) *
        run p G k
    else run p G k

theorem run_succ (p : Fin n → Fin n) (G : Matrix (Fin n) (Fin n) R) (k : ℕ) (h : k < n) :
    run p G (k + 1) =
      stepOp ⟨k, h⟩ (p ⟨k, h⟩) (run p G k) (Ring.inverse (run p G k (p ⟨k, h⟩) ⟨k, h⟩)) *
        run p G k := by
  simp only [run, h, ↓reduceDIte]

theorem run_succ_of_not (p : Fin n → Fin n) (G : Matrix (Fin n) (Fin n) R) (k : ℕ) (h : ¬k < n) :
    run p G (k + 1) = run p G k := by
  simp only [run, h, ↓reduceDIte]

/-- Each of the first `k` pivots lies at or below the diagonal and is a unit. -/
def Valid (p : Fin n → Fin n) (G : Matrix (Fin n) (Fin n) R) (k : ℕ) : Prop :=
  ∀ j (h : j < n), j < k → j ≤ (p ⟨j, h⟩).val ∧ IsUnit (run p G j (p ⟨j, h⟩) ⟨j, h⟩)

theorem valid_succ (p : Fin n → Fin n) (G : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    Valid p G (k + 1) ↔ Valid p G k ∧
      ∀ h : k < n, k ≤ (p ⟨k, h⟩).val ∧ IsUnit (run p G k (p ⟨k, h⟩) ⟨k, h⟩) := by
  constructor
  · intro hv
    exact ⟨fun j h hj => hv j h (Nat.lt_succ_of_lt hj), fun h => hv k h (Nat.lt_succ_self k)⟩
  · rintro ⟨hv, hk⟩ j h hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · exact hv j h hlt
    · exact hk h

/-- A valid itinerary clears the first `k` columns with `k (n - 1)` additions and `k`
exchanges. -/
theorem run_spec (p : Fin n → Fin n) (G : Matrix (Fin n) (Fin n) R) :
    ∀ k, k ≤ n → Valid p G k → ∃ E : Matrix (Fin n) (Fin n) R, Elim (k * (n - 1)) k E ∧
      E * G = run p G k ∧ ColCleared k (run p G k) ∧
      ∀ j : Fin n, j.val < k → IsUnit (run p G k j j) := by
  intro k
  induction k with
  | zero =>
    intro _ _
    refine ⟨1, by rw [Nat.zero_mul]; exact Elim.one, by rw [Matrix.one_mul]; rfl,
      fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk hv
    have hkn : k < n := hk
    obtain ⟨hv', hpk⟩ := (valid_succ p G k).mp hv
    obtain ⟨hle, hu⟩ := hpk hkn
    obtain ⟨E, hE, hEG, hM, hunits⟩ := ih (by omega) hv'
    obtain ⟨hF, hcl, hdiag, hKK⟩ := step ⟨k, hkn⟩ (p ⟨k, hkn⟩) hle (run p G k) hM _
      (Ring.mul_inverse_cancel _ hu)
    rw [run_succ p G k hkn]
    refine ⟨stepOp ⟨k, hkn⟩ (p ⟨k, hkn⟩) (run p G k)
      (Ring.inverse (run p G k (p ⟨k, hkn⟩) ⟨k, hkn⟩)) * E, ?_,
      by rw [Matrix.mul_assoc, hEG], hcl, fun j hj => ?_⟩
    · have h := hF.mul hE
      have e : n - 1 + k * (n - 1) = (k + 1) * (n - 1) := by ring
      rw [e, Nat.add_comm 1 k] at h
      exact h
    · by_cases hjk : j.val < k
      · rw [hdiag j hjk]
        exact hunits j hjk
      · have hj' : j = ⟨k, hkn⟩ := Fin.ext (show j.val = k by omega)
        rw [hj', hKK]
        exact hu

/-- **The fallback normal form along an itinerary.** -/
theorem itinerary_form (p : Fin n → Fin n) (G : Matrix (Fin n) (Fin n) R) (hv : Valid p G n) :
    ∃ (E : Matrix (Fin n) (Fin n) R) (d : Fin n → R),
      Elim (n * (n - 1)) n E ∧ E * G = diagonal d ∧ ∀ i, IsUnit (d i) := by
  obtain ⟨E, hE, hEG, hM, hu⟩ := run_spec p G n le_rfl hv
  refine ⟨E, fun i => run p G n i i, hE, ?_, fun i => hu i i.isLt⟩
  rw [hEG]
  ext i j
  by_cases hij : i = j
  · rw [hij, diagonal_apply_eq]
  · rw [diagonal_apply_ne _ hij]
    exact hM i j j.isLt hij

/-- The run reads only the pivot rows of the columns it has processed. -/
theorem run_congr (p p' : Fin n → Fin n) (G : Matrix (Fin n) (Fin n) R) :
    ∀ k, (∀ i : Fin n, i.val < k → p i = p' i) → run p G k = run p' G k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    have ih' := ih fun i hi => h i (Nat.lt_succ_of_lt hi)
    by_cases hk : k < n
    · rw [run_succ p G k hk, run_succ p' G k hk, ih', h ⟨k, hk⟩ (Nat.lt_succ_self k)]
    · rw [run_succ_of_not p G k hk, run_succ_of_not p' G k hk, ih']

/-- An invertible matrix over a local ring has a valid itinerary. -/
theorem exists_valid [IsLocalRing R] (G : Matrix (Fin n) (Fin n) R) (hG : IsUnit G.det) :
    ∀ k, k ≤ n → ∃ p : Fin n → Fin n, Valid p G k := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨id, fun j _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk
    have hkn : k < n := hk
    obtain ⟨p, hv⟩ := ih (by omega)
    obtain ⟨E, hE, hEG, hM, _⟩ := run_spec p G k (by omega) hv
    have hdet : IsUnit (run p G k).det := by
      rw [← hEG, det_mul]
      exact hE.isUnit_det.mul hG
    obtain ⟨i₀, hi₀, hp⟩ := exists_unit hkn hM hdet
    have hagree (j : ℕ) (hj : j ≤ k) :
        run (Function.update p ⟨k, hkn⟩ i₀) G j = run p G j :=
      run_congr _ _ G j fun i hi =>
        Function.update_of_ne (fun h => absurd (congrArg Fin.val h) (by show i.val ≠ k; omega)) _ _
    refine ⟨Function.update p ⟨k, hkn⟩ i₀, (valid_succ _ G k).mpr ⟨fun j h hj => ?_, fun h => ?_⟩⟩
    · have hne : (⟨j, h⟩ : Fin n) ≠ ⟨k, hkn⟩ := fun e =>
        absurd (congrArg Fin.val e) (by show j ≠ k; omega)
      rw [hagree j (by omega), Function.update_of_ne hne]
      exact hv j h hj
    · rw [hagree k le_rfl, Function.update_self]
      exact ⟨hi₀, hp⟩

theorem exists_itinerary [IsLocalRing R] (G : Matrix (Fin n) (Fin n) R) (hG : IsUnit G.det) :
    ∃ p : Fin n → Fin n, Valid p G n :=
  exists_valid G hG n le_rfl

/-! ### Residue classes -/

theorem inverse_unique {x y : R} (h : x * y = 1) : Ring.inverse x = y := by
  have hx : IsUnit x := isUnit_iff_exists_inv.mpr ⟨y, h⟩
  calc Ring.inverse x = Ring.inverse x * (x * y) := by rw [h, mul_one]
    _ = y := by rw [← mul_assoc, Ring.inverse_mul_cancel x hx, one_mul]

theorem map_inverse (φ : R →+* S) {x : R} (hx : IsUnit x) :
    φ (Ring.inverse x) = Ring.inverse (φ x) :=
  (inverse_unique (by rw [← map_mul, Ring.mul_inverse_cancel x hx, map_one])).symm

theorem colMat_map (φ : R →+* S) (K : Fin n) (f : Fin n → R) :
    φ.mapMatrix (colMat K f) = colMat K fun i => φ (f i) := by
  ext a b
  simp only [RingHom.mapMatrix_apply, map_apply, colMat, of_apply]
  split_ifs <;> simp

theorem swapMat_map (φ : R →+* S) (i j : Fin n) :
    φ.mapMatrix (swapMat i j : Matrix (Fin n) (Fin n) R) = swapMat i j := by
  ext a b
  simp only [RingHom.mapMatrix_apply, map_apply, swapMat, of_apply]
  split_ifs <;> simp

theorem stepOp_map (φ : R →+* S) (K i₀ : Fin n) (M : Matrix (Fin n) (Fin n) R) (p' : R) :
    φ.mapMatrix (stepOp K i₀ M p') = stepOp K i₀ (φ.mapMatrix M) (φ p') := by
  have hf : (fun i => φ (if i ∈ Finset.univ.erase K then M (Equiv.swap K i₀ i) K * p' else 0)) =
      fun i => if i ∈ Finset.univ.erase K then φ.mapMatrix M (Equiv.swap K i₀ i) K * φ p'
        else 0 := by
    funext i
    split_ifs <;> simp [RingHom.mapMatrix_apply]
  rw [stepOp, stepOp, map_mul, map_sub, map_one, colMat_map, swapMat_map, hf]

/-- Elimination along a valid itinerary commutes with a ring homomorphism. -/
theorem run_map (φ : R →+* S) (p : Fin n → Fin n) (G : Matrix (Fin n) (Fin n) R) :
    ∀ k, Valid p G k → φ.mapMatrix (run p G k) = run p (φ.mapMatrix G) k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hv
    obtain ⟨hv', hpk⟩ := (valid_succ p G k).mp hv
    have ih' := ih hv'
    by_cases hk : k < n
    · obtain ⟨_, hu⟩ := hpk hk
      have he : φ (run p G k (p ⟨k, hk⟩) ⟨k, hk⟩) =
          run p (φ.mapMatrix G) k (p ⟨k, hk⟩) ⟨k, hk⟩ := by
        rw [← ih']
        rfl
      rw [run_succ p G k hk, run_succ p _ k hk, map_mul, stepOp_map, map_inverse φ hu, he, ih']
    · rw [run_succ_of_not p G k hk, run_succ_of_not p _ k hk, ih']

/-- Validity of an itinerary is read off the image under a homomorphism that reflects units. -/
theorem valid_map_iff (φ : R →+* S) (hφ : ∀ a, IsUnit (φ a) → IsUnit a) (p : Fin n → Fin n)
    (G : Matrix (Fin n) (Fin n) R) : ∀ k, Valid p G k ↔ Valid p (φ.mapMatrix G) k := by
  intro k
  induction k with
  | zero =>
    constructor <;> intro _ j _ hj <;> exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
    have he (hv : Valid p G k) (h : k < n) : φ (run p G k (p ⟨k, h⟩) ⟨k, h⟩) =
        run p (φ.mapMatrix G) k (p ⟨k, h⟩) ⟨k, h⟩ := by
      rw [← run_map φ p G k hv]
      rfl
    rw [valid_succ, valid_succ]
    constructor
    · rintro ⟨hv, hk⟩
      refine ⟨ih.mp hv, fun h => ?_⟩
      obtain ⟨hle, hu⟩ := hk h
      refine ⟨hle, ?_⟩
      rw [← he hv h]
      exact hu.map φ
    · rintro ⟨hv, hk⟩
      have hv0 := ih.mpr hv
      refine ⟨hv0, fun h => ?_⟩
      obtain ⟨hle, hu⟩ := hk h
      rw [← he hv0 h] at hu
      exact ⟨hle, hφ _ hu⟩

/-- **One itinerary per residue class.** Two matrices with the same image under a homomorphism
that reflects units have the same valid itineraries. -/
theorem valid_congr (φ : R →+* S) (hφ : ∀ a, IsUnit (φ a) → IsUnit a) (p : Fin n → Fin n)
    {G G' : Matrix (Fin n) (Fin n) R} (h : φ.mapMatrix G = φ.mapMatrix G') (k : ℕ) :
    Valid p G k ↔ Valid p G' k := by
  rw [valid_map_iff φ hφ p G k, h, ← valid_map_iff φ hφ p G' k]

end IntegerMultBounds.MathlibTM2.Cover.Itinerary
