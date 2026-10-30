module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedPreparedInputRelease

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

/-- The concrete owned buffers and controls required after recovery. -/
structure PackedPreparedReleaseReady {A : ℕ} (V N w rows : ℕ) (xs : List GaussianInt)
    (input tail : List (Fin (A+4))) (S : Stacks 248 A) : Prop where
  inputLength : input.length = N*w
  source : ∃ residual : List (Fin (A+4)), residual.length = N*w ∧ S.R 110 = residual++(input++tail)
  length : S.R 165 = binSyms V N
  factorWidth : (S.R 174).length = w
  width : (S.R 130).length = w
  count : (S.R 139).length = xs.length
  rows : (S.R 140).length = rows
  page : S.R 138 = cstream A w xs
  clean : ∀ i ∈ ([0,1,2,104,105,109,246,247,242,243] : List (Fin 248)), S.R i = []

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 248 Q A U}

theorem packedPreparedInputRelease_ready_exec (V N w q W boundaryCount rows : ℕ)
    (hNV : N < 2^V) (xs : List GaussianInt) (input tail : List (Fin (A+4)))
    (v : HS 248 Q A U) (S : Stacks 248 A)
    (hready : PackedPreparedReleaseReady V N w rows xs input tail S)
    (hbank : PackedPreparedBank q w W boundaryCount (embStk packedBoundaryRecoveryBase S)) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ packedRecoveryReleaseCost xs.length rows w+packedInputAdvanceCost V N w+(2*w+3) ∧
      Exec body packedPreparedInputRelease (mk v S) n (mk v' (packedPreparedInputReleased S tail)) ∧
      PackedPreparedBank q w W boundaryCount
        (embStk packedBoundaryRecoveryBase (packedPreparedInputReleased S tail)) ∧
      (∀ bo hf df, PackedBoundaryFactorPages bo hf df (embStk packedBoundaryRecoveryBase S) →
        PackedBoundaryFactorPages bo hf df
          (embStk packedBoundaryRecoveryBase (packedPreparedInputReleased S tail))) := by
  obtain ⟨residual,hlen,hsource⟩ := hready.source
  exact packedPreparedInputRelease_exec V N w q W boundaryCount rows hNV xs residual input tail
    hlen hready.inputLength v S hready.length hready.factorWidth hready.width hsource
    hready.count hready.rows hready.page hready.clean hbank

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
