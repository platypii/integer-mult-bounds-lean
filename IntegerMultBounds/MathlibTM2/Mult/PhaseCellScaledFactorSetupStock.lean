module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScaledFactorPrepared
public import IntegerMultBounds.MathlibTM2.Host.ClosedProgramStock

/-! Scaled factor setup is native header construction. Charge its own traffic,
separately from the shared numerical factorization reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

theorem UnarySetup.program_noCalls {T : ℕ} (ops : List (UnarySetup.Op T)) :
    WordCmd.NoCalls (UnarySetup.program (P := P) (Q := Q) (A := A) (U := U) ops) := by
  induction ops with
  | nil => trivial
  | cons op ops ih =>
    refine ⟨?_,ih⟩
    cases op <;>
      simp [UnarySetup.Op.program, umul, umulSym, udiv, unaryProduct, ucopy,
        scanP, scanR, drainR, moveR, whileR, uclear, WordCmd.NoCalls]

@[irreducible] def scaledFactorSetupPush (factor : ℕ) : ℕ :=
  mnProgPush (scaledFactorSetup (P := P) (Q := Q) (A := A) (U := U) factor)

theorem scaledFactorSetup_native (factor : ℕ) :
    mnNativePushBound (scaledFactorSetupPush (P := P) (Q := Q) (A := A) (U := U) factor)
      (scaledFactorSetup (P := P) (Q := Q) (A := A) (U := U) factor) := by
  have hcounter : WordCmd.NoCalls (boundaryFactorCountersFromWidth (P := P) (Q := Q) (A := A) (U := U)) := by
    unfold boundaryFactorCountersFromWidth
    exact WordCmd.noCalls_of_native (embProg_native _ _ _ (WordCmd.empty_native _))
  unfold scaledFactorSetupPush
  apply WordCmd.native_of_noCalls _ le_rfl
  simp [scaledFactorSetup, scaledFactorHeaderSetup, scaledFactorDimensions,
    boundaryFactorMultiplierSetup, generateWordWidth, boundaryFactorConstants,
    boundaryFactorNewtonHeader, boundaryFactorNewtonPrelude, UnarySetup.program_noCalls,
    boundaryFactorSeed, unarySize, ldrLoop, ldrStep, setPowerWord, movePrefix, transfer,
    ucopy, umulSym, scanR, drainR, moveR, whileR, uclear, copyR, hcounter, WordCmd.NoCalls]

theorem scaledFactorSetup_exec_within_of_exec {factor p q band N n : ℕ}
    {v v' : HS 224 Q A U} {S F : Stacks 224 A}
    (he : Exec body (scaledFactorSetup factor) (mk v S) n (mk v' F))
    (ht : n ≤ scaledFactorSetupCost factor p q band N) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
      scaledFactorSetupPush (P := P) (Q := Q) (A := A) (U := U) factor *
        scaledFactorSetupCost factor p q band N) depth
      (scaledFactorSetup factor) (mk v S) n (mk v' F) := by
  apply mn_native_exec_within he _ (scaledFactorSetup_native factor) depth _
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ ht) _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
