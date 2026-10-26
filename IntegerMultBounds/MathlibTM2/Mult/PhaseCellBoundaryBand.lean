module

public import IntegerMultBounds.NLogN.PhaseCellHaloBoundaryFold
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryTolerance

/-! Mask computed boundary entries to the proved local band without worsening accuracy. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open Finset IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.SchurDominance

variable {s : ℕ} [NeZero s]

noncomputable def bandBoundaryTable (B : Finset (ZMod s)) (W : ℕ)
    (Sh : Matrix (ZMod s) (ZMod s) ℝ) : Matrix (ZMod s) (ZMod s) ℝ :=
  fun i j => if FoldBRel s B W i j then Sh i j else 0

omit [NeZero s] in
theorem bandBoundaryTable_support (B : Finset (ZMod s)) (W : ℕ)
    (Sh : Matrix (ZMod s) (ZMod s) ℝ) (i j : ZMod s)
    (h : bandBoundaryTable B W Sh i j ≠ 0) : FoldBRel s B W i j := by
  by_contra hband
  exact h (by simp [bandBoundaryTable,hband])

omit [NeZero s] in
theorem bandBoundaryTable_error (B : Finset (ZMod s)) (W : ℕ)
    (S Sh : Matrix (ZMod s) (ZMod s) ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hS : ∀ i ∈ B, ∀ j ∈ B, S i j ≠ 0 → FoldBRel s B W i j)
    (hSh : ∀ i ∈ B, ∀ j ∈ B, |Sh i j-S i j| ≤ ε) :
    ∀ i ∈ B, ∀ j ∈ B, |bandBoundaryTable B W Sh i j-S i j| ≤ ε := by
  intro i hi j hj
  by_cases hband : FoldBRel s B W i j
  · simpa [bandBoundaryTable,hband] using hSh i hi j hj
  · have hzero : S i j = 0 := by
      by_contra hne
      exact hband (hS i hi j hj hne)
    simpa [bandBoundaryTable,hband,hzero] using hε

/-- The number of potentially stored entries in any folded band row. -/
theorem foldBRel_row_card (B : Finset (ZMod s)) (W : ℕ) (i : ZMod s) :
    (B.filter fun j => FoldBRel s B W i j).card ≤ 2*W+1 := by
  have hsub : (B.filter fun j => FoldBRel s B W i j).image (bFoldPos s B) ⊆
      Icc (bFoldPos s B i-W) (bFoldPos s B i+W) := by
    intro n hn
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hn
    have h := (mem_filter.mp hj).2
    unfold FoldBRel at h
    exact mem_Icc.mpr ⟨by omega,h.2⟩
  have hh := card_le_card hsub
  rw [card_image_of_injective _ (bFoldPos_injective s B),Nat.card_Icc] at hh
  omega

/-- All local boundary tables can use the actual halo's folded band; discarded
entries have exact target zero, so masking spends no additional error. -/
theorem haloBoundaryTable_entry_error {t p u a b target rhsExp : ℕ}
    (hst : s < t) (Sh : Matrix (ZMod s) (ZMod s) ℝ)
    (hSh : ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b,
      ∀ j ∈ haloBoundary s t (PhaseCellBand.width p u) a b,
      |Sh i j-(run (realMatrix s t p u) (haloVertices s a b)
        (haloInterior s t (PhaseCellBand.width p u) a b).toList).1 i j| ≤
        1/(2 : ℝ)^boundaryTableBits p target rhsExp
          (haloBoundary s t (PhaseCellBand.width p u) a b).card) :
    ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b,
      ∀ j ∈ haloBoundary s t (PhaseCellBand.width p u) a b,
      |bandBoundaryTable (haloBoundary s t (PhaseCellBand.width p u) a b)
          (12*PhaseCellBand.width p u+1) Sh i j-
        (run (realMatrix s t p u) (haloVertices s a b)
          (haloInterior s t (PhaseCellBand.width p u) a b).toList).1 i j| ≤
        1/(2 : ℝ)^boundaryTableBits p target rhsExp
          (haloBoundary s t (PhaseCellBand.width p u) a b).card :=
  bandBoundaryTable_error _ _ _ _ _ (by positivity)
    (fun _ hi _ hj h => halo_schur_foldBRel hst p u a b hi hj h) hSh

/-- Rounded elimination of the masked computed table preserves the local band. -/
theorem bandBoundaryTable_factors (B : Finset (ZMod s)) (W : ℕ)
    (Sh : Matrix (ZMod s) (ZMod s) ℝ)
    (rd : ℝ → ℝ) (mul : ℝ → ℝ → ℝ) (hrd0 : rd 0 = 0) (hmul0 : ∀ x, mul 0 x = 0) :
    (∀ i k, luLr rd mul (bandBoundaryTable B W Sh) B (bFoldOrder s B) i k ≠ 0 →
      i = k ∨ (FoldBRel s B W i k ∧ bFoldPos s B k < bFoldPos s B i)) ∧
    (∀ k j, luUr rd mul (bandBoundaryTable B W Sh) B (bFoldOrder s B) k j ≠ 0 →
      FoldBRel s B W k j ∧ bFoldPos s B k ≤ bFoldPos s B j) :=
  boundary_factors_fold s B W _ (fun i _ j _ h => bandBoundaryTable_support B W Sh i j h)
    rd mul hrd0 hmul0

/-- The rounded factor pages have the same per-row storage bound as the masked
input table, including the lower factor's unit diagonal. -/
theorem bandBoundaryTable_factor_rows (B : Finset (ZMod s)) (W : ℕ)
    (Sh : Matrix (ZMod s) (ZMod s) ℝ)
    (rd : ℝ → ℝ) (mul : ℝ → ℝ → ℝ) (hrd0 : rd 0 = 0) (hmul0 : ∀ x, mul 0 x = 0)
    (i : ZMod s) :
    (B.filter fun j => luLr rd mul (bandBoundaryTable B W Sh) B (bFoldOrder s B) i j ≠ 0).card ≤ 2*W+1 ∧
    (B.filter fun j => luUr rd mul (bandBoundaryTable B W Sh) B (bFoldOrder s B) i j ≠ 0).card ≤ 2*W+1 := by
  obtain ⟨hL,hU⟩ := bandBoundaryTable_factors B W Sh rd mul hrd0 hmul0
  constructor
  · apply (card_le_card (show (B.filter fun j => luLr rd mul (bandBoundaryTable B W Sh) B
        (bFoldOrder s B) i j ≠ 0) ⊆ B.filter (fun j => FoldBRel s B W i j) from ?_)).trans
      (foldBRel_row_card B W i)
    intro j hj
    obtain ⟨hjB,hne⟩ := mem_filter.mp hj
    apply mem_filter.mpr
    refine ⟨hjB,?_⟩
    rcases hL i j hne with heq | hrel
    · subst j
      unfold FoldBRel
      omega
    · exact hrel.1
  · apply (card_le_card (show (B.filter fun j => luUr rd mul (bandBoundaryTable B W Sh) B
        (bFoldOrder s B) i j ≠ 0) ⊆ B.filter (fun j => FoldBRel s B W i j) from ?_)).trans
      (foldBRel_row_card B W i)
    intro j hj
    obtain ⟨hjB,hne⟩ := mem_filter.mp hj
    exact mem_filter.mpr ⟨hjB,(hU i j hne).1⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
