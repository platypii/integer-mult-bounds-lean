import IntegerMultBounds.Networks.GaussianDyadic
import IntegerMultBounds.Networks.GroupedCircuit
import IntegerMultBounds.Networks.CircuitTriples

/-! Gaussian-dyadic closure of the actual rational motif coefficients and of
simultaneous grouped scalar updates. This complements the binary phase edge
precision bounds; it does not implement Gaussian arithmetic on tapes. -/

namespace IntegerMultBounds.Networks.GaussianDyadic

theorem grid_list_sum {n : ℕ} (zs : List ℂ) (hz : ∀ z ∈ zs, Grid n z) : Grid n zs.sum := by
  induction zs with
  | nil => exact grid_zero n
  | cons z zs ih =>
    exact grid_add (hz z (List.mem_cons_self ..)) (ih (fun w hw => hz w (List.mem_cons_of_mem z hw)))

/-- A whole simultaneous group increases precision once by the maximum
coefficient precision, independently of its number of rows and terms. -/
theorem grid_evaluateRows {ι : Type*} [DecidableEq ι] {n d : ℕ}
    (rows : List (Circuit.Gate ι ℂ)) (r : ι → ℂ) (hr : ∀ i, Grid n (r i))
    (hc : ∀ g ∈ rows, ∀ p ∈ g.terms, Grid d p.2) :
    ∀ i, Grid (n + d) (GroupedCircuit.evaluateRows rows r i) := by
  intro i
  apply grid_add (grid_mono (Nat.le_add_right n d) (hr i))
  apply grid_list_sum
  intro z hz
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hz
  split_ifs
  · apply grid_list_sum
    intro w hw
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
    simpa only [Nat.add_comm] using grid_mul (hc g hg p hp) (hr p.1)
  · exact grid_zero _

theorem grid_runGroups {ι : Type*} [DecidableEq ι] {n d : ℕ}
    (gs : List (GroupedCircuit.Group ι ℂ)) (r : ι → ℂ) (hr : ∀ i, Grid n (r i))
    (hc : ∀ g ∈ gs, ∀ row ∈ g.rows, ∀ p ∈ row.terms, Grid d p.2) :
    ∀ i, Grid (n + gs.length * d) (GroupedCircuit.runGroups gs r i) := by
  induction gs generalizing n r with
  | nil => simpa only [GroupedCircuit.runGroups, List.length_nil, Nat.zero_mul, Nat.add_zero] using hr
  | cons g gs ih =>
    have hh := ih (GroupedCircuit.evaluate g r)
      (grid_evaluateRows g.rows r hr (hc g (List.mem_cons_self ..)))
      (fun g hg => hc g (List.mem_cons_of_mem _ hg))
    simpa only [GroupedCircuit.runGroups, List.length_cons, Nat.add_mul, Nat.one_mul,
      Nat.add_assoc, Nat.add_comm d] using hh

theorem grid_centralCoeff {h n : ℕ} (L : Fin n → Finset (Fin h)) (s t : Fin n) :
    Grid 1 ((Circuit.centralCoeff L s t : ℚ) : ℂ) := by
  have hh := grid_half (grid_sub (grid_int ((L s ∩ L t).card : ℤ)) (grid_int 1))
  simpa [Circuit.centralCoeff] using hh

theorem grid_complexCopy {h n a : ℕ} {L : Fin n → Finset (Fin h)}
    (e : Fin a ≃ Circuit.ComplexPair L) (p : Fin a) (t : Fin n) :
    Grid 0 ((Circuit.complexCopy e p t : ℚ) : ℂ) := by
  simp only [Circuit.complexCopy]
  split_ifs <;> norm_cast
  · simpa using grid_int 1
  · exact grid_zero 0

theorem grid_complexInject {h n a : ℕ} {L : Fin n → Finset (Fin h)}
    (e : Fin a ≃ Circuit.ComplexPair L) (s : Fin n) (p : Fin a) :
    Grid 1 ((Circuit.complexInject e s p : ℚ) : ℂ) := by
  simp only [Circuit.complexInject]
  split_ifs
  · simpa using grid_neg (grid_centralCoeff L s (e p).val.2)
  · simpa using grid_zero 1

theorem grid_complexGather {h n : ℕ} (L : Fin n → Finset (Fin h))
    (i : Fin (h + 1)) (t : Fin n) :
    Grid 0 ((Circuit.complexGather L i t : ℚ) : ℂ) := by
  induction i using Fin.lastCases with
  | last => simpa [Circuit.complexGather] using grid_int 1
  | cast j =>
    simp only [Circuit.complexGather, Fin.lastCases_castSucc]
    split_ifs
    · simpa using grid_int 1
    · simpa using grid_zero 0

theorem grid_complexScatter {h n : ℕ} (L : Fin n → Finset (Fin h))
    (s : Fin n) (i : Fin (h + 1)) :
    Grid 1 ((Circuit.complexScatter L s i : ℚ) : ℂ) := by
  induction i using Fin.lastCases with
  | last => simpa [Circuit.complexScatter] using grid_neg (grid_half (grid_int 1))
  | cast j =>
    simp only [Circuit.complexScatter, Fin.lastCases_castSucc]
    split_ifs
    · simpa using grid_half (grid_int 1)
    · simpa using grid_zero 1

end IntegerMultBounds.Networks.GaussianDyadic
