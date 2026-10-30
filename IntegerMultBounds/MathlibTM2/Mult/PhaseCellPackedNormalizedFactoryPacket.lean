module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedDescriptorWords
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedFactoryInputBank

/-! The normalized caller's ordinary packet, including its constructed native
factory headers. Full analytic and geometry readiness remains a separate proof. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {A : ℕ}

noncomputable def packedNormalizedFactoryBank (H : Stacks 242 A)
    (p u l targetOut s t a b V : ℕ) [NeZero s] : Stacks 242 A :=
  let band := PhaseCellBand.width p u
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (targetOut+1)) 2
    (haloBoundary s t band a b).card
  let target := initialSchurTarget p u bits 2
  packedFactoryInputBank H (2^15*p) (executionStagePrecision p l target 2+1)
    (executionPrecision p l target 2) l s t u band a b V

/-- Native loop readiness is established for the actual selected header words. -/
theorem packedNormalizedFactoryBank_native_ready (H : Stacks 242 A)
    (p u l targetOut s t a b V : ℕ) [NeZero s] :
    let band := PhaseCellBand.width p u
    let bits := boundaryTableBits p (boundaryRecoveryTarget p (targetOut+1)) 2
      (haloBoundary s t band a b).card
    let target := initialSchurTarget p u bits 2
    let S := packedNormalizedFactoryBank H p u l targetOut s t a b V
    LengthKeyReady (2^15*p) (executionStagePrecision p l target 2+1)
      (executionPrecision p l target 2) l s t u band 0 0 (S.R 110)
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg (embStk preparedBoundaryCoreReg
          (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S))))))) := by
  dsimp only [packedNormalizedFactoryBank]
  rw [packedFactoryInputBank_source]
  exact packedFactoryInputBank_ready _ _ _ _ _ _ _ _ _ _ _ _

/-- All ordinary words for the normalized complex batch, constructed from
numeric parameters and field data. No arbitrary private-bank contents remain. -/
noncomputable def packedNormalizedFactoryPacketWords (H : Stacks 242 A)
    (B V p u l targetOut s t a b coreWidth k radius W : ℕ) [NeZero s]
    (Fs : List (ZMod s → GaussianInt)) : Fin 325 → List (Fin (A+4)) :=
  packedNormalizedPacketWords (packedNormalizedFactoryBank H p u l targetOut s t a b V)
    B V p u l targetOut s t a b coreWidth k radius W Fs

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
