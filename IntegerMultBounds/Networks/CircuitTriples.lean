import IntegerMultBounds.Networks.Circuit

/-! Rational coefficient matrices of the complex motif, with explicit finite bank enumerations.
The supplied equivalences only enumerate the physical wires; no algebraic or
runtime property of the circuit is assumed. -/

namespace IntegerMultBounds.Networks.Circuit

section MatrixComposition
variable {R : Type*} [CommRing R]

theorem reconstruct_of_coefficients {n a c : ℕ} (V : Fin a → Fin n → R)
    (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
    (coeff : ∀ s t, (∑ p, J s p * V p t) + (∑ i, H s i * G i t) =
      if s = t then 1 else 0) (X : Fin n → R) :
    mv J (mv V X) + mv H (mv G X) = X := by
  ext s
  simp only [Pi.add_apply, mv, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i t => H s i * (G i t * X t))]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  rw [← Finset.sum_add_distrib]
  simp_rw [← add_mul, coeff]
  simp
end MatrixComposition

/-- Exactly the ordered neighboring pairs specified for the complex motif. -/
abbrev ComplexPair {h n : ℕ} (L : Fin n → Finset (Fin h)) :=
  {p : Fin n × Fin n // L p.1 ≠ L p.2 ∧ Even (L p.1 ∩ L p.2).card}

/-- The coefficient delivered through the central wires. -/
def centralCoeff {h n : ℕ} (L : Fin n → Finset (Fin h)) (s t : Fin n) : ℚ :=
  (((L s ∩ L t).card : ℚ) - 1) / 2

/-- Copy one logical source into each of its side wires. -/
def complexCopy {h n a : ℕ} {L : Fin n → Finset (Fin h)}
    (e : Fin a ≃ ComplexPair L) : Fin a → Fin n → ℚ :=
  fun p t => if (e p).val.2 = t then 1 else 0

/-- Feed each side wire to its target with the prescribed cancelling coefficient. -/
def complexInject {h n a : ℕ} {L : Fin n → Finset (Fin h)}
    (e : Fin a ≃ ComplexPair L) : Fin n → Fin a → ℚ :=
  fun s p => if (e p).val.1 = s then -centralCoeff L s (e p).val.2 else 0

/-- The last central wire is the all-source sum; the others are coordinate sums. -/
def complexGather {h n : ℕ} (L : Fin n → Finset (Fin h)) : Fin (h + 1) → Fin n → ℚ :=
  fun i t => Fin.lastCases 1 (fun j => if j ∈ L t then 1 else 0) i

/-- Half the coordinate sums at a target, minus half the all-source sum. -/
def complexScatter {h n : ℕ} (L : Fin n → Finset (Fin h)) : Fin n → Fin (h + 1) → ℚ :=
  fun s i => Fin.lastCases (-(1 / 2)) (fun j => if j ∈ L s then 1 / 2 else 0) i

theorem complex_central_coeff {h n : ℕ} (L : Fin n → Finset (Fin h)) (s t : Fin n) :
    (∑ i, complexScatter L s i * complexGather L i t) = centralCoeff L s t := by
  rw [Fin.sum_univ_castSucc]
  simp only [complexScatter, complexGather, Fin.lastCases_castSucc, Fin.lastCases_last]
  have hh (i : Fin h) :
      (if i ∈ L s then (1 : ℚ) / 2 else 0) * (if i ∈ L t then 1 else 0) =
        if i ∈ L s ∩ L t then (1 : ℚ) / 2 else 0 := by
    split_ifs <;> simp_all
  simp_rw [hh]
  rw [← Finset.sum_filter]
  have hf : Finset.univ.filter (fun i => i ∈ L s ∩ L t) = L s ∩ L t := by ext; simp
  rw [hf]
  simp [centralCoeff]
  ring

theorem complex_side_coeff {h n a : ℕ} {L : Fin n → Finset (Fin h)}
    (e : Fin a ≃ ComplexPair L) (s t : Fin n) :
    (∑ p, complexInject e s p * complexCopy e p t) =
      if L s ≠ L t ∧ Even (L s ∩ L t).card then -centralCoeff L s t else 0 := by
  have term (p : Fin a) : complexInject e s p * complexCopy e p t =
      if (e p).val = (s, t) then -centralCoeff L s t else 0 := by
    by_cases hs : (e p).val.1 = s <;> by_cases ht : (e p).val.2 = t <;>
      simp [complexInject, complexCopy, hs, ht, Prod.ext_iff]
  simp_rw [term]
  by_cases hst : L s ≠ L t ∧ Even (L s ∩ L t).card
  · let q : ComplexPair L := ⟨(s, t), hst⟩
    have he (p : Fin a) : (e p).val = (s, t) ↔ p = e.symm q := by
      change (e p).val = q.val ↔ _
      rw [← Subtype.ext_iff, ← e.eq_symm_apply]
    simp [he, hst]
  · have he (p : Fin a) : (e p).val ≠ (s, t) := by
      intro hp
      apply hst
      have := (e p).property
      simpa only [hp] using this
    simp [he, hst]

/-- The explicitly enumerated sparse matrices reconstruct the whole source
bank. Only the wire enumeration and the three-element label property are inputs. -/
theorem complex_reconstruct {h n a : ℕ} {L : Fin n → Finset (Fin h)}
    (e : Fin a ≃ ComplexPair L) (hinj : Function.Injective L)
    (hcard : ∀ i, (L i).card = 3) (X : Fin n → ℚ) :
    mv (complexInject e) (mv (complexCopy e) X) +
      mv (complexScatter L) (mv (complexGather L) X) = X := by
  apply reconstruct_of_coefficients
  intro s t
  rw [complex_side_coeff, complex_central_coeff, add_comm]
  change complexCoefficient (L s) (L t) = _
  rw [complexCoefficient_eq _ _ (hcard s) (hcard t)]
  simp only [hinj.eq_iff]

/-- The complex motif executed over rational scalars, with arbitrary dirty side and
central banks. The only premises describe which finite physical wires exist. -/
theorem complex_dirty_run {h n a s : ℕ} {L : Fin n → Finset (Fin h)}
    (e : Fin a ≃ ComplexPair L) (hinj : Function.Injective L)
    (hcard : ∀ i, (L i).card = 3) (X Y : Fin n → ℚ)
    (A : Fin a → ℚ) (C : Fin (h + 1) → ℚ) (S : Fin s → ℚ) :
    run (dirty (complexCopy e) (complexGather L) (complexInject e) (complexScatter L))
      (banks X Y A C S) = banks X (Y + X) A C S := by
  exact dirty_run_shear _ _ _ _ (complex_reconstruct e hinj hcard) X Y A C S

end IntegerMultBounds.Networks.Circuit

