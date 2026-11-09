module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUniformPublicationSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedReplicaPublication

/-! One concrete uniform-core publication program, shared by all placements
and axis callers. Header and control generation are explicit chronological phases. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Q K : ℕ} {P U : Type}

def uniformDyadicPublicationProgram (hstates : FixedStreamedBank.stateCount ≤ Q)
    (exponent packet pad tmp saved : Fin tapeCount) {dst : Fin tapeCount}
    (pub : PreparedPublicationPlan tapeCount (extra 1) dst) (clock lineRows : Fin tapeCount) :
    Pr P tapeCount Q (prime+K) U :=
  (.seq (.seq (pub.uniformSetup realRows (headerReg 86) (headerReg 87) (headerReg 90))
          (.seq (.seq generatedPublicationHeadersProgram (.seq (.seq (ownedPrefixPadding exponent packet (extra 1) pad tmp saved (pairSym (prime+K) false false))
          (PackedTranspose.program hstates)) (pub.replicaProgram clock lineRows))) (clearWords generatedPublicationHeaderRegisters))) (clearWords (pub.uniformSetupHeaders (headerReg 90))))

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
