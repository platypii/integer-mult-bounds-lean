import IntegerMultBounds.Networks.GaussianBoundedArithmetic

/-! Concrete numerator bounds for every scalar coefficient of the actual
complex cancellation motifs; no coefficient closure contract is supplied. -/
namespace IntegerMultBounds.Networks.GaussianPrecision

 theorem bounded_centralCoeff {h n : ℕ} (L : Fin n → Finset (Fin h)) (s t : Fin n) :
    BoundedGrid 1 (h+1) ((Circuit.centralCoeff L s t : ℚ) : ℂ) := by
  have hc : (L s ∩ L t).card≤h := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (L s ∩ L t)
  have hi : |((L s ∩ L t).card : ℤ)-1|≤((h+1:ℕ):ℤ) := by
    rw [abs_le]
    push_cast
    omega
  have hh := bounded_half (bounded_int (((L s ∩ L t).card : ℤ)-1) (h+1) hi)
  simpa [Circuit.centralCoeff] using hh

theorem bounded_complexCopy {h n a : ℕ} {L : Fin n → Finset (Fin h)}
    (e : Fin a ≃ Circuit.ComplexPair L) (p : Fin a) (t : Fin n) :
    BoundedGrid 0 1 ((Circuit.complexCopy e p t : ℚ) : ℂ) := by
  simp only [Circuit.complexCopy]
  split_ifs
  · simpa using bounded_int 1 1 (by norm_num)
  · simpa using bounded_zero 0 1

theorem bounded_complexInject {h n a : ℕ} {L : Fin n → Finset (Fin h)}
    (e : Fin a ≃ Circuit.ComplexPair L) (s : Fin n) (p : Fin a) :
    BoundedGrid 1 (h+1) ((Circuit.complexInject e s p : ℚ) : ℂ) := by
  simp only [Circuit.complexInject]
  split_ifs
  · simpa using bounded_neg (bounded_centralCoeff L s (e p).val.2)
  · simpa using bounded_zero 1 (h+1)

theorem bounded_complexGather {h n : ℕ} (L : Fin n → Finset (Fin h))
    (i : Fin (h+1)) (t : Fin n) :
    BoundedGrid 0 1 ((Circuit.complexGather L i t : ℚ) : ℂ) := by
  induction i using Fin.lastCases with
  | last => simpa [Circuit.complexGather] using bounded_int 1 1 (by norm_num)
  | cast j =>
    simp only [Circuit.complexGather,Fin.lastCases_castSucc]
    split_ifs
    · simpa using bounded_int 1 1 (by norm_num)
    · simpa using bounded_zero 0 1

theorem bounded_complexScatter {h n : ℕ} (L : Fin n → Finset (Fin h))
    (s : Fin n) (i : Fin (h+1)) :
    BoundedGrid 1 1 ((Circuit.complexScatter L s i : ℚ) : ℂ) := by
  induction i using Fin.lastCases with
  | last =>
    simpa [Circuit.complexScatter] using bounded_neg (bounded_half (bounded_int 1 1 (by norm_num)))
  | cast j =>
    simp only [Circuit.complexScatter,Fin.lastCases_castSucc]
    split_ifs
    · simpa using bounded_half (bounded_int 1 1 (by norm_num))
    · simpa using bounded_zero 1 1

end IntegerMultBounds.Networks.GaussianPrecision
