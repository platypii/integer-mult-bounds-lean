module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicGatherTranspose
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedPadGatherPayload
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireRoutedGather

/-! One fixed gather-routing program reuses the codec buffers for padding
and dummy-prefix retirement. Four retained unary dimensions are preserved. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
namespace PackedTranspose
noncomputable section
open FixedStreamedBank
variable {Q K : ℕ} {P U : Type}

def realRows : Fin tapeCount := base (callerGenerator 80)
def capacityRows : Fin tapeCount := base (callerGenerator 81)
def packetWidth : Fin tapeCount := base (callerGenerator 82)
def replicaCount : Fin tapeCount := base (callerGenerator 83)

def padGatherProgram : Pr P tapeCount Q (prime+K) U :=
  generatedPrefixPadRows realRows capacityRows packetWidth (extra 5) (extra 6) (extra 4) (extra 1)
    (extra 0) (extra 3) (extra 2) replicaCount (planeReg false) (pairSym (prime+K) false false)

def retireGatherProgram : Pr P tapeCount Q (prime+K) U :=
  retireDummyBatches realRows capacityRows replicaCount packetWidth (extra 5) (extra 6) (extra 4) (extra 3) (extra 2) (extra 1)

def gatherProgram (hstates : FixedStreamedBank.stateCount ≤ Q) : Pr P tapeCount Q (prime+K) U :=
  .seq padGatherProgram (.seq (program hstates) retireGatherProgram)

theorem padGather_registers :
    [realRows,capacityRows,packetWidth,extra 5,extra 6,extra 4,extra 1,extra 0,extra 3,extra 2,replicaCount,planeReg false].Nodup := by
  have hk : 117 ≤ kernelT := by change 117 ≤ FixedStreamedBank.tapeCount+117; omega
  simp [List.nodup_cons,realRows,capacityRows,packetWidth,replicaCount,callerGenerator,
    TransposeRegisterPlacement.generator,planeReg,base,extra,owned,callerWorker,
    TransposeRegisterPlacement.worker,workerReg,reg_val,pay,Fin.ext_iff]
  omega

theorem retireGather_registers :
    [realRows,capacityRows,replicaCount,packetWidth,extra 5,extra 6,extra 4,extra 3,extra 2,extra 1].Nodup := by
  have hr := padGather_registers
  regs_ne hr
  regs_nodup

end
end PackedTranspose
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
