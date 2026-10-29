module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedPreparedResidualSolve

/-! The reusable physical workspace needed by normalization, solve and unscale.
Factor data and RHS semantics are supplied separately. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

structure PackedBoundarySolveWorkspace {A : ℕ} (q : ℕ) (S : Stacks 242 A) : Prop where
  left : ∀ i : Fin 224, (embStk packedBoundaryFactorReg S).L (preparedBoundaryCoreReg i) = []
  mul : ∀ i : Fin 64, (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg S)).R
    (boundaryFactorMulReg i) = []
  precision : ((embStk packedBoundaryFactorReg S).R 119).length = q
  exponent : (embStk packedBoundaryFactorReg S).R 223 = []
  scalar : (embStk packedBoundaryFactorReg S).R 184 = []
  table : (embStk packedBoundaryFactorReg S).R 220 = []
  padding : (embStk packedBoundaryFactorReg S).R 221 = []
  swap : (embStk packedBoundaryFactorReg S).R 225 = []

/-- Publishing a solved RHS preserves the numerical workspace. -/
theorem PackedBoundarySolveWorkspace.publish {A q : ℕ} {S : Stacks 242 A}
    (h : PackedBoundarySolveWorkspace q S) (output : List (Fin (A+4))) :
    PackedBoundarySolveWorkspace q
      {S with R := (Function.update (Function.update S.R 143 []) 238 (output++S.R 238))} := by
  constructor
  · exact h.left
  · intro i
    have hi := i.isLt
    simpa [embStk,preparedBoundaryCoreReg,packedBoundaryFactorReg,boundaryFactorMulReg,
      Fin.ext_iff,show i.val ≠ 140 by omega,show i.val ≠ 143 by omega,
      show i.val ≠ 206 by omega,show i.val < 154 by omega,
      show i.val ≠ 238 by omega] using h.mul i
  · exact h.precision
  · exact h.exponent
  · exact h.scalar
  · exact h.table
  · exact h.padding
  · exact h.swap

/-- The retained numerical state supplies every old-bank temporary used by
boundary recovery. The remaining inverse-fold counters live in fresh ports. -/
theorem packedBoundaryRecovery_clean {A q w W N : ℕ} {S : Stacks 242 A}
    (hwork : PackedBoundarySolveWorkspace q S)
    (hready : BoundarySolveReady (boundaryFactorState
      (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg S))) q w W N) :
    ∀ i ∈ ([231,239,198,237,222,225,215,229] : List (Fin 242)), S.R i = [] := by
  intro i hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hready.empty .dout (by decide)
  · exact hwork.swap
  · exact hwork.scalar
  · exact hwork.exponent
  · exact hready.empty .ya (by decide)
  · exact hready.empty .xs (by decide)
  · exact hready.empty .tC (by decide)
  · exact hready.empty .ac2 (by decide)

/-- Recovery uses the solver's retained word width directly. -/
theorem packedBoundaryRecovery_width {A q w W N : ℕ} {S : Stacks 242 A}
    (hready : BoundarySolveReady (boundaryFactorState
      (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg S))) q w W N) :
    (S.R 174).length = w :=
  hready.ready.wn

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
