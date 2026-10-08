import IntegerMultBounds.Networks.GroupedRouting

/-! Exact sparse incidences of the local motif groups. In particular, no side
wire disappears under its nonzero cancelling coefficient, and each side wire
belongs to precisely its owning copy and injection groups. -/

namespace IntegerMultBounds.Networks.MotifSupport

open Circuit GroupedCircuit

theorem bitInject_ne_zero {h n a : ℕ} {L : Fin n → Finset (Fin h)}
    (e : Fin a ≃ BitPair L) (s : Fin n) (p : Fin a) :
    bitInject e s p ≠ 0 ↔ (e p).val.1 = s := by
  simp [bitInject]

theorem complex_pair_coefficient_ne_zero {h n : ℕ} {L : Fin n → Finset (Fin h)}
    (p : ComplexPair L) : centralCoeff L p.val.1 p.val.2 ≠ 0 := by
  intro hz
  have hn : ((L p.val.1 ∩ L p.val.2).card : ℚ) = 1 := by
    unfold centralCoeff at hz
    linarith
  have hn' : (L p.val.1 ∩ L p.val.2).card = 1 := by exact_mod_cast hn
  obtain ⟨k, hk⟩ := p.property.2
  omega

theorem complexInject_ne_zero {h n a : ℕ} {L : Fin n → Finset (Fin h)}
    (e : Fin a ≃ ComplexPair L) (s : Fin n) (p : Fin a) :
    complexInject e s p ≠ 0 ↔ (e p).val.1 = s := by
  by_cases hs : (e p).val.1 = s
  · subst s
    simp [complexInject, complex_pair_coefficient_ne_zero (e p)]
  · simp [complexInject, hs]

section Incidences
variable {R : Type*} [CommRing R] [DecidableEq R]
    {n a c s : ℕ}

private theorem side_x (i : Fin a) (j : Fin n) :
    (side i : Role n a c s) ≠ x j := by simp [side, x]
private theorem y_side (i : Fin n) (j : Fin a) :
    (y i : Role n a c s) ≠ side j := by simp [y, side]
private theorem y_center (i : Fin n) (j : Fin c) :
    (y i : Role n a c s) ≠ center j := by simp [y, center]
private theorem center_x (i : Fin c) (j : Fin n) :
    (center i : Role n a c s) ≠ x j := by simp [center, x]

/-- Each side wire is touched only in the copy group of its unique owner. -/
theorem copy_side (owner : Fin a → Fin n) (r : R) (hr : r ≠ 0) (j : Fin n) (p : Fin a) :
    (side p : Role n a c s) ∈ touched (copyGroup side x owner r side_x j) ↔ owner p = j := by
  rw [copyGroup_touched _ _ _ _ hr]
  simp [side, x]

theorem copy_data (owner : Fin a → Fin n) (r : R) (hr : r ≠ 0) (j t : Fin n) :
    (x t : Role n a c s) ∈ touched (copyGroup side x owner r side_x j) ↔
      t = j ∧ ∃ p, owner p = j := by
  rw [copyGroup_touched _ _ _ _ hr]
  simp [side, x]

/-- A side wire's injection incidence is precisely the nonzero matrix entry. -/
theorem inject_side (J : Fin n → Fin a → R) (i : Fin n) (p : Fin a) :
    (side p : Role n a c s) ∈ touched (faninGroup (y i) side (J i) (y_side i)) ↔ J i p ≠ 0 := by
  rw [faninGroup_touched]
  simp [side, y]

theorem inject_data (J : Fin n → Fin a → R) (i j : Fin n) :
    (y j : Role n a c s) ∈ touched (faninGroup (y i) side (J i) (y_side i)) ↔ j = i := by
  rw [faninGroup_touched]
  simp [side, y]

theorem scatter_center (H : Fin n → Fin c → R) (j : Fin c) :
    (center j : Role n a c s) ∈ touched (matrixGroup y center H y_center) ↔ ∃ i, H i j ≠ 0 := by
  rw [matrixGroup_touched]
  simp [center, y]

theorem scatter_data (H : Fin n → Fin c → R) (i : Fin n) :
    (y i : Role n a c s) ∈ touched (matrixGroup y center H y_center) := by
  rw [matrixGroup_touched]
  exact Or.inl ⟨i, rfl⟩

theorem gather_center (G : Fin c → Fin n → R) (i : Fin c) :
    (center i : Role n a c s) ∈ touched (matrixGroup center x G center_x) := by
  rw [matrixGroup_touched]
  exact Or.inl ⟨i, rfl⟩

theorem gather_data (G : Fin c → Fin n → R) (j : Fin n) :
    (x j : Role n a c s) ∈ touched (matrixGroup center x G center_x) ↔ ∃ i, G i j ≠ 0 := by
  rw [matrixGroup_touched]
  simp [center, x]

end Incidences

/-- Negating a matrix for undo does not alter its physical sparse support. -/
theorem matrix_touched_neg {ι R : Type*} [CommRing R] [DecidableEq R]
    {n m : ℕ} (dst : Fin n → ι) (src : Fin m → ι) (M : Fin n → Fin m → R)
    (sep : ∀ i j, dst i ≠ src j) (k : ι) :
    k ∈ touched (matrixGroup dst src (-M) sep) ↔ k ∈ touched (matrixGroup dst src M sep) := by
  simp only [matrixGroup_touched, Pi.neg_apply, neg_ne_zero]

end IntegerMultBounds.Networks.MotifSupport
