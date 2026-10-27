module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCachedArithmetic
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellHaloRingSizing

/-! The selected retained-family interior arithmetic costs O(t*M(p)).
Shared control and address work remain an explicit separate charge. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def familyHaloControlCost (p l s t u target rhsExp a b : ℕ) : ℕ :=
  let band := PhaseCellBand.width p u
  let P := 2^15*p
  let N := executionStagePrecision p l target rhsExp+1
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let V := weightWorkspaceWidth P q w t u
  initializeHaloLengthKeysBound P N q l s t u band a b+
    ((haloLengthCandidates s t band a b).map (fun L =>
      cachedHaloClassSharedCost p l L s t u target rhsExp a b)).sum+
    (t-s+1)*(3*tblC V V+49*V+49)+2*(V+w)+207

theorem familyHaloInteriorGeometryCost_eq (p l s t u target rhsExp a b : ℕ) :
    familyHaloInteriorGeometryCost p l s t u target rhsExp a b =
      familyHaloControlCost p l s t u target rhsExp a b+
        (haloInterior s t (PhaseCellBand.width p u) a b).card*
          (cachedBatchCoordinateCost p l target rhsExp+44*executionWidth p l target rhsExp)+
        (t-s+1)*cachedBatchCellCost p l target rhsExp := by
  dsimp only [familyHaloInteriorGeometryCost,familyHaloControlCost,cachedHaloClassCellCost]
  ring

/-- Actual first-pass precision and a derived ring length give a uniform arithmetic allowance. -/
theorem familyInteriorGeometry_selected_fast_le (ct cG : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p u target s t a b : ℕ, ∀ [NeZero s],
      1 ≤ p → s < t → PhaseCellBand.width p u ≤ s →
      1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1 → target ≤ ct*p → Nat.size (2*s+1) ≤ cG*p →
      let l := haloInverseRingLog s t
      let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
      let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
      let stage := initialSchurTarget p u bits 2
      (familyHaloInteriorGeometryCost p l s t u stage 2 a b : ℝ) ≤
        (familyHaloControlCost p l s t u stage 2 a b : ℝ)+C*(t : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨K,hK,hfast⟩ := inverseCachedArithmetic_selected_fast_le 20 ct cG 20
  refine ⟨9*K,by positivity,?_⟩
  intro p u target s t a b _ hp hst hband hθ ht hgeometry
  dsimp only
  let l := haloInverseRingLog s t
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  let stage := initialSchurTarget p u bits 2
  let I := (haloInterior s t (PhaseCellBand.width p u) a b).card
  let w := executionWidth p l stage 2
  let r := 2^l
  obtain ⟨hl,hr⟩ := haloInverseRingLog_bounds hp hst hθ
  obtain ⟨hc,hd⟩ := hfast p u l target s t a b hp hband hl ht hgeometry hr
  have hI : I ≤ t := by
    have hh : I ≤ s := by simpa [I] using Finset.card_le_univ (s := haloInterior s t (PhaseCellBand.width p u) a b)
    omega
  have hpad := haloInverseRing_paddedVolume_le hst
  have hsum : (I : ℝ)+((t-s+1 : ℕ) : ℝ)*(r : ℝ) ≤ 9*(t : ℝ) := by
    have hIR : (I : ℝ) ≤ t := by exact_mod_cast hI
    have hpR : ((t-s+1 : ℕ) : ℝ)*(r : ℝ) ≤ 8*(t : ℝ) := by exact_mod_cast hpad
    linarith only [hIR,hpR]
  have hMp : 0 ≤ (p : ℝ)^(129/128 : ℝ) := by positivity
  have harithmetic :
      (I : ℝ)*((cachedBatchCoordinateCost p l stage 2+44*w : ℕ) : ℝ)+
        ((t-s+1 : ℕ) : ℝ)*(cachedBatchCellCost p l stage 2 : ℝ) ≤
      9*K*(t : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
    calc
      _ ≤ (I : ℝ)*(K*(p : ℝ)^(129/128 : ℝ))+
          ((t-s+1 : ℕ) : ℝ)*(K*(r : ℝ)*(p : ℝ)^(129/128 : ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg I))
          (mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg _))
      _ = K*((I : ℝ)+((t-s+1 : ℕ) : ℝ)*(r : ℝ))*(p : ℝ)^(129/128 : ℝ) := by ring
      _ ≤ K*(9*(t : ℝ))*(p : ℝ)^(129/128 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hK) hMp
      _ = _ := by ring
  rw [familyHaloInteriorGeometryCost_eq]
  push_cast at harithmetic ⊢
  dsimp only [I,w,l,stage,bits,N] at harithmetic
  linarith only [harithmetic]

/-- Attach the selected geometry allowance to the actual executed pass ledger. -/
theorem familyInterior_selected_fast_le (ct cG : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A p u target s t a b : ℕ, ∀ [NeZero s],
      1 ≤ p → s < t → PhaseCellBand.width p u ≤ s →
      1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1 → target ≤ ct*p → Nat.size (2*s+1) ≤ cG*p →
      let l := haloInverseRingLog s t
      let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
      let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
      let stage := initialSchurTarget p u bits 2
      (familySolveHaloInteriorCost A p l s t u stage 2 a b : ℝ) ≤
        (familyHaloControlCost p l s t u stage 2 a b : ℝ)+C*(t : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,hC,hfast⟩ := familyInteriorGeometry_selected_fast_le ct cG
  refine ⟨C,hC,?_⟩
  intro A p u target s t a b _ hp hst hband hθ ht hgeometry
  have h := hfast p u target s t a b hp hst hband hθ ht hgeometry
  have hcost := familySolveHaloInteriorCost_geometry_le hst A p (haloInverseRingLog s t) u
    (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
      (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2 a b
  exact (Nat.cast_le (α := ℝ)).mpr hcost |>.trans h

end IntegerMultBounds.MathlibTM2.Cost
