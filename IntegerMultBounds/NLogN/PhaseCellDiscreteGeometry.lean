module

public import IntegerMultBounds.NLogN.PhaseCellInteriorCover

/-! # Computable ambient phase and interior metadata

The integer quotient includes the existing nearest-rounding tie convention.
No real comparison or choice is required to enumerate one phase's interior.
This is numerical metadata construction, not an executed tape scan.
-/

@[expose] public section

namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- Nearest-rounding phase as an exact signed integer quotient. -/
def phaseIndex (s t : ℕ) (j : ℤ) : ℤ :=
  (2 * ((t : ℤ) - s) * j + s) / (2 * s)

theorem phaseIndex_eq {s t : ℕ} (hs : 0 < s) (j : ℤ) :
    phaseIndex s t j = PhaseCell.phase s t j := by
  let numerator := 2 * ((t : ℤ) - s) * j + s
  let denominator := 2 * (s : ℤ)
  have hd : 0 < denominator := by dsimp [denominator]; omega
  let x : PhaseCellScan.State := ⟨numerator / denominator, numerator % denominator⟩
  have hx : PhaseCellScan.Invariant s ((t : ℤ) - s) j x := by
    refine ⟨?_, Int.emod_nonneg _ (ne_of_gt hd), Int.emod_lt_of_pos _ hd⟩
    dsimp [x]
    rw [Int.emod_def]
  exact PhaseCellScan.phase_eq hs hx

/-- Membership in the original ambient interior; artificial halo cuts are not
silently substituted into this definition. -/
def isInterior (s t w j : ℕ) : Bool :=
  decide (w ≤ j ∧ j + w < s ∧ phaseIndex s t ((j : ℤ) - w) = phaseIndex s t ((j : ℤ) + w))

theorem isInterior_spec {s t : ℕ} [NeZero s] (w : ℕ) (j : ZMod s) :
    isInterior s t w j.val = true ↔ PhaseCellMatrix.Interior s t w j := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  simp only [isInterior, decide_eq_true_eq, phaseIndex_eq hs, PhaseCellMatrix.Interior]

/-- Enumerate the interior vertices of one ambient phase in physical order. -/
def interiorIndices (s t w : ℕ) (phase : ℤ) : List ℕ :=
  (List.range s).filter (fun j => isInterior s t w j && decide (phaseIndex s t j = phase))

theorem mem_interiorIndices {s t : ℕ} [NeZero s] (w : ℕ) (phase : ℤ) (j : ZMod s) :
    j.val ∈ interiorIndices s t w phase ↔
      PhaseCellMatrix.Interior s t w j ∧ PhaseCellMatrix.cell s t j = phase := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  simp only [interiorIndices, List.mem_filter, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq, isInterior_spec, phaseIndex_eq hs, PhaseCellMatrix.cell]
  exact and_iff_right (ZMod.val_lt j)

/-- Enumeration has no duplicate physical coordinates. -/
theorem interiorIndices_nodup (s t w : ℕ) (phase : ℤ) :
    (interiorIndices s t w phase).Nodup :=
  List.Nodup.filter _ (List.nodup_range (n := s))

/-- Every enumerated physical coordinate remains inside the ambient axis. -/
theorem interiorIndices_lt (s t w : ℕ) (phase : ℤ) {j : ℕ}
    (hj : j ∈ interiorIndices s t w phase) : j < s :=
  List.mem_range.mp (List.mem_of_mem_filter hj)

/-- The complete ambient interior set is computed from physical indices. -/
def interiorSet (s t w : ℕ) : Finset (ZMod s) :=
  List.toFinset (List.map (fun j : ℕ => (j : ZMod s)) (List.filter (isInterior s t w) (List.range s)))

theorem mem_interiorSet {s t : ℕ} [NeZero s] (w : ℕ) (j : ZMod s) :
    j ∈ interiorSet s t w ↔ PhaseCellMatrix.Interior s t w j := by
  simp only [interiorSet, List.mem_toFinset, List.mem_map, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨n, ⟨hns, hn⟩, rfl⟩
    have hval : (n : ZMod s).val = n := ZMod.val_cast_of_lt hns
    apply (isInterior_spec w (n : ZMod s)).mp
    simpa only [hval] using hn
  · intro hj
    exact ⟨j.val, ⟨ZMod.val_lt j, (isInterior_spec w j).mpr hj⟩, by simp⟩

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
