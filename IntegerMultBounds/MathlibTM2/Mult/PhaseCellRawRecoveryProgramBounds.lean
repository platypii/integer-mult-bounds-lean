module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRecoveryResourceBudgets

/-! Fixed program bounds are shared by every raw job and every selected axis. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

structure RawRecoveryProgramBounds (Q A : ℕ) (U : Type) where
  hR : rpStates ≤ Q
  hQ : SS.states ≤ Q
  hA : 96 ≤ A
  R : ℕ
  K : ℕ
  c : ℕ
  M : ℕ
  push : BoundarySolvePushBounds (A := A) (U := U) hQ
  hpushR : mnProgPush (rpProg (P := Empty) (Q := Q) (A := A) (U := U)
    Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ R
  hpushK : mnProgPush (cmulBlock cr (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
    mul mul_injective (by decide) hQ cr)) ≤ K
  hpush : mnNativePushBound c (replicaBoundaryRhs (P := Empty) (Q := Q) (A := A) (U := U))
  hpushM : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
    mul mul_injective (by decide) hQ cr) ≤ M

namespace RawRecoveryProgramBounds
variable {Q A s : ℕ} {U : Type} [NeZero s]

noncomputable def stock (b : RawRecoveryProgramBounds Q A U) (r : RawRecoveryJob s) : ℕ :=
  r.stockBudget b.hR b.hQ b.push b.c b.M b.R b.K

theorem batch_nonempty (b : RawRecoveryProgramBounds Q A U) (v : HS 392 Q A U) (r : RawRecoveryJob s) :
    Nonempty (ReplicaRecoveryBatch r.problem r.target r.solution) :=
  r.batch_nonempty b.hR b.hQ b.hA b.R b.K b.hpushR b.hpushK b.push b.c b.hpush b.M b.hpushM v

end RawRecoveryProgramBounds
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
