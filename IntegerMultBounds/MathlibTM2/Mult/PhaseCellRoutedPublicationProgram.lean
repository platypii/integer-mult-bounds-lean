module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedRoutedClassOutput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedPublicationTranspose
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedPublicationPages
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoringReplicaPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationControlPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCorePublicationGroups

/-! Fixed routed publication code and its costs. All dimensions and rows remain
runtime data; the standard wiring reuses the checked publication bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open FixedStreamedBank ScalarPlacement
noncomputable section
variable {Q K s width : ℕ} {P U : Type}

/-- Fixed publication code: dimensions are retained tape data. -/
def routedPublicationProgram (hstates : FixedStreamedBank.stateCount ≤ Q) (numerical : Fin tapeCount)
    (exportCount exportReplicas exportPacket exportClock exportVolume exportSaved exportTmp
      exponent packet pad tmp saved : Fin tapeCount) (e : Fin 117 → Fin tapeCount)
    (clock clockSave padRows wordWidth retireCount savedControl gap dst acc trash pubTmp lineRows outAcc pubSaved : Fin tapeCount) :
    Pr P tapeCount Q (prime+K) U :=
  (.seq (PackedExactBatch.generatedExport numerical exportCount exportReplicas exportPacket exportClock exportVolume (extra 1) exportSaved exportTmp) (.seq (.seq (ownedPrefixPadding exponent packet (extra 1) pad tmp saved (pairSym (prime+K) false false))
          (program hstates))
          (.seq (embProg e Empty.elim (prepareReplicaPublicationPages (P := Empty)))
            (.seq (restoringReplicaPublication clock clockSave padRows wordWidth retireCount (e 92) savedControl gap (e 103) (extra 1) dst acc trash pubTmp lineRows outAcc pubSaved)
              (clearWords [e 103,e 92])))))

def routedPublicationTimeCost (hstates : FixedStreamedBank.stateCount ≤ Q)
    (a b L V W N : ℕ) (g : CorePublicationClass s width) (hw : 0 < width) : ℕ :=
  (PackedExactBatch.generatedExportCost N (2^b) (L*W))+(((6*(2^(a+b)*(L*W))+4*(N*((2^b)*(L*W)))+4*(L*W)+9*(a+b)+14)+
        (26*(2^a*(2^b*(L*W)))+24+2*restoringTimeCost hstates a b (L*W) V))+
        ((prepareReplicaPublicationPagesCost V s g.length W g.indices.length+
          (replicaPublicationCost (2^b) s (2^a-N) g.length W+6*(2^b)+6))+
          (2*(g.length*W+(gatherControls (prime+K) ((coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).gaps W)).length)+5)))

def routedPublicationStock (hstates : FixedStreamedBank.stateCount ≤ Q)
    (a b L V W N : ℕ) (g : CorePublicationClass s width) : ℕ :=
  (max (2*PackedExactBatch.generatedExportCost N (2^b) (L*W)) ((2*(6*(2^(a+b)*(L*W))+4*(N*((2^b)*(L*W)))+4*(L*W)+9*(a+b)+14)+
          (40*(2^a*(2^b*(L*W)))+38+restoringStockAllowance hstates a b (L*W) V))+
          (mnProgPush (prepareReplicaPublicationPages (P := Empty) (Q := Q) (A := prime+K) (U := U))*
            prepareReplicaPublicationPagesCost V s g.length W g.indices.length+2*(replicaPublicationCost (2^b) s (2^a-N) g.length W+6*(2^b)+6))))

/-- The physical publication bank already used by the selected caller. -/
def standardRoutedPublicationProgram (hstates : FixedStreamedBank.stateCount ≤ Q) :
    Pr P tapeCount Q (prime+K) U :=
  routedPublicationProgram hstates numericalPort
    (publicationReg 36) (publicationReg 54) (publicationReg 52) (publicationReg 69)
    (publicationReg 68) (publicationReg 71) (publicationReg 72)
    (publicationReg 51) (publicationReg 52) (publicationReg 58) (publicationReg 65) (publicationReg 66)
    publicationPageBank (publicationReg 54) (publicationReg 67) (publicationReg 53) (publicationReg 34)
    (publicationReg 73) (publicationReg 74) (publicationReg 75) ambientPort
    (publicationReg 76) (publicationReg 77) (publicationReg 78) (publicationReg 79)
    (publicationReg 80) (publicationReg 81)

theorem standardExport_registers :
    [publicationReg 36,publicationReg 54,publicationReg 52,publicationReg 69,publicationReg 68,
      numericalPort,extra 1,publicationReg 71,publicationReg 72].Nodup := by
  have hr := publicationCopy_registers
  regs_ne hr
  regs_nodup

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
