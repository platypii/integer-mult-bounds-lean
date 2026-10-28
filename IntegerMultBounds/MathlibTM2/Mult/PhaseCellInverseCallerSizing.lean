module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseScalarSetup

/-! Choose scalar word width from ordinary dimensions, without a supplied boundary cardinality. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem inversePrecisionRoom_mono {N M : ℕ} (p l target band : ℕ) (hNM : N ≤ M) :
    inversePrecisionRoom p l target N band ≤ inversePrecisionRoom p l target M band := by
  have hs := Nat.size_le_size hNM
  dsimp [inversePrecisionRoom,inverseExecutionExponent]
  omega

def inverseCallerWorkspace (p u l target s t : ℕ) : ℕ :=
  let band := PhaseCellBand.width p u
  (64*(p+1)+u)+(8*(t+1)^2+2*band+8)+inversePrecisionRoom p l target s band

def inverseCallerWordWidth (p u l target s t : ℕ) : ℕ :=
  Nat.size (inverseCallerWorkspace p u l target s t)

theorem inverseCallerWordWidth_fits_cuts (p u l target s t a b : ℕ) [NeZero s] :
    let W := inverseCallerWordWidth p u l target s t
    64*(p+1)+u < 2^W ∧
      8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^W ∧
      inversePrecisionRoom p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card
        (PhaseCellBand.width p u) < 2^W := by
  dsimp only
  have hN : (haloBoundary s t (PhaseCellBand.width p u) a b).card ≤ s := by
    have h := Finset.card_le_univ (haloBoundary s t (PhaseCellBand.width p u) a b)
    rwa [ZMod.card] at h
  have hroom := inversePrecisionRoom_mono p l target (PhaseCellBand.width p u) hN
  have hwidth : inverseCallerWorkspace p u l target s t < 2^inverseCallerWordWidth p u l target s t :=
    Nat.lt_size_self _
  dsimp only [inverseCallerWorkspace] at hwidth
  omega

theorem inverseCallerWordWidth_fits (p u l target s t : ℕ) [NeZero s] :
    let W := inverseCallerWordWidth p u l target s t
    64*(p+1)+u < 2^W ∧
      8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^W ∧
      inversePrecisionRoom p l target (haloBoundary s t (PhaseCellBand.width p u) 0 s).card
        (PhaseCellBand.width p u) < 2^W := by
  exact inverseCallerWordWidth_fits_cuts p u l target s t 0 s

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
