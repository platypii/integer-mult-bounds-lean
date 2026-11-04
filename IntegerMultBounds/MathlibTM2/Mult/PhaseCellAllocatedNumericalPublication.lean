module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedNumericalPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationHeaderPlacement
public import IntegerMultBounds.MathlibTM2.Host.EmbedInputOutputStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputTableUpdate
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputTableRetirement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedOutputPublicationCopy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedClassScatter
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOwnedPrefixPaddingStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedArchiveTileData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientPaddingData

/-! Concrete publication allocation beside the selected caller prefix.
Only the result and ambient ports are redirected; all other tapes are private. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
namespace PackedTranspose
noncomputable section
open FixedStreamedBank ScalarPlacement
variable {T Q K s t width : ℕ} [NeZero s] [NeZero t] {P U : Type}

theorem allocated_publish_outputs_exec_within (body : P → Pr P (T+tapeCount) Q (prime+K) U)
    (inputPort outputPort : Fin T) (hports : inputPort ≠ outputPort)
    (hstates : FixedStreamedBank.stateCount ≤ Q) (a b L V : ℕ)
    (batch : PackedExactBatch (prime+K) s t (2^b) L)
    (outputs : List (List (Fin (prime+K+4))))
    (hgood : List.Forall₂ PackedNormalizedJob.output batch.records outputs)
    (copyCount copySavedCount copyWidth archive copySaved copyTmp : Fin tapeCount)
    (hcopyReg : [copyCount,copySavedCount,copyWidth,numericalPort,archive,extra 1,copySaved,copyTmp].Nodup)
    (g : CorePublicationClass s width) (hkeys : batch.records.map (fun r => r.k) = g.indices)
    (hcoreWidth : ∀ r ∈ batch.records, r.coreWidth = width) (hw : 0 < width)
    (hlength : L = g.length) (hw1 : 1 ≤ batch.W)
    (hpacket : 0 < L*batch.W) (hbits : a+b < V) (hfit : (L*batch.W)*2^(a+b) < 2^V) (hA : 4 ≤ prime+K)
    (exponent packet pad tmp saved : Fin tapeCount)
    (hpadReg : [exponent,packet,extra 1,pad,tmp,saved].Nodup)
    (hcapacity : batch.records.length ≤ 2^a) (depth : ℕ)
    (ambient : Fin (2^b) → List (Fin (prime+K+4))) (hambient : ∀ j, (ambient j).length = s*batch.W)
    (clock clockSave padRows wordWidth retireCount savedControl gap acc trash pubTmp lineRows outAcc pubSaved : Fin tapeCount)
    (hreg : [clock,clockSave,padRows,wordWidth,retireCount,(publicationPageBank 92),savedControl,gap,(publicationPageBank 103),extra 1,ambientPort,acc,trash,pubTmp,lineRows,outAcc,pubSaved].Nodup)
    (outputTail : List (Fin (prime+K+4)))
    (input : Fin 3 → Fin tapeCount)
    (loadWidth loadZero : Fin tapeCount)
    (hloadWidth : ∀ r, publicationGeometryBank r ≠ loadWidth) (hloadZero : ∀ r, publicationGeometryBank r ≠ loadZero)
    (hloadInput : ∀ i r, publicationGeometryBank r ≠ input i)
    (hreadOff : loadWidth ≠ numericalPort ∧ loadZero ≠ numericalPort ∧ ∀ i, input i ≠ numericalPort)
    (value : Fin tapeCount → ℕ) (hinputFit : ∀ i, value (input i) < 2^V)
    (hvalues : ∀ i, value (input i) = ![a,b,L*batch.W] i)
    (v : HS (T+tapeCount) Q (prime+K) U) (S : Stacks (T+tapeCount) (prime+K))
    (hnumericalBlank : (embStk (publicationPlacement inputPort outputPort) S).R numericalPort = [])
    (htableBlank : ∀ r, (embStk (publicationPlacement inputPort outputPort) S).R (publicationGeometryBank r) = [])
    (hwLoad : ((embStk (publicationPlacement inputPort outputPort) S).R loadWidth).length = V)
    (hzLoad : (embStk (publicationPlacement inputPort outputPort) S).R loadZero = [])
    (hsrcLoad : ∀ i, (embStk (publicationPlacement inputPort outputPort) S).R (input i) = binSyms V (value (input i))) :
    let M := loadedInputTable publicationGeometryBank input V value (embStk (publicationPlacement inputPort outputPort) S)
    ∀ (_ : (M.R exponent).length = a+b) (_ : (M.R packet).length = L*batch.W)
    (_ : M.R pad = []) (_ : M.R tmp = []) (_ : M.R saved = [])
    (_ : M.R (base (callerGenerator 106)) = [])
    (_ : ∀ r, M.R (base (callerGenerator (originReg r))) = [])
    (_ : M.R (base (callerGenerator 116)) = []) (_ : ∀ i, M.L i = [])
    (_ : ∀ i, i ≠ workerReg (reg pay) → i ≠ FixedStreamedBank.control 7 → M.R (base (callerWorker i)) = [])
    (_ : M.R (extra 1) = [])
    (_ : (M.R copyCount).length = batch.records.length)
    (_ : (M.R copyWidth).length = (2^b)*L*batch.W)
    (_ : ∀ i ∈ [copySavedCount,archive,copySaved,copyTmp], M.R i = [])
    (_ : M.R (extra 4) = [])
    (_ : ∀ i ∈ [planeReg false,planeReg true,extra 2,extra 3,extra 5,extra 6], M.R i = [])
    (_ : M.R ambientPort = (List.ofFn ambient).flatten++outputTail)
    (_ : (M.R clock).length = 2^b) (_ : M.R clockSave = [])
    (_ : (M.R padRows).length = (2^a-batch.records.length)*g.length)
    (_ : (M.R wordWidth).length = batch.W) (_ : (M.R lineRows).length = s)
    (_ : batch.W < 2^V) (_ : s < 2^V) (_ : s*batch.W < 2^V)
    (originTail : List (Fin (prime+K+4)))
    (_ : (M.R (publicationPageBank 115)).length = V) (_ : (M.R (publicationPageBank 94)).length = batch.W)
    (_ : (M.R (publicationPageBank 102)).length = g.length)
    (_ : M.R (publicationPageBank 109) =
      (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).origins.flatMap (binSyms V)++originTail)
    (_ : M.R (publicationPageBank 116) = List.replicate
      (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).origins.length tick)
    (_ : ∀ i : Fin 117, i.val < 19 → M.R (publicationPageBank i) = [])
    (_ : ∀ i ∈ [(88 : Fin 117),89,90,91,92,103,104,105,106,107], M.R (publicationPageBank i) = [])
    (_ : ∀ i ∈ [retireCount,savedControl,gap,acc,trash,pubTmp,pubSaved], M.R i = [])
    (_ : M.R outAcc = []),
    ∃ rows : batch.Rows, ∃ v' n, v'.user = v.user ∧
      n ≤ ((28*V+33)+((reverseCopyRowsCost batch.records.length ((2^b)*L*batch.W)+2*outputs.reverse.flatten.length+2)+(((6*(2^(a+b)*(L*batch.W))+4*(batch.records.length*((2^b)*(L*batch.W)))+4*(L*batch.W)+9*(a+b)+14)+
        (26*(2^a*(2^b*(L*batch.W)))+24+2*restoringTimeCost hstates a b (L*batch.W) V))+
        ((prepareReplicaPublicationPagesCost V s g.length batch.W g.indices.length+
          (replicaPublicationCost (2^b) s (2^a-batch.records.length) g.length batch.W+6*(2^b)+6))+
          (2*(g.length*batch.W+(gatherControls (prime+K) ((coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).gaps batch.W)).length)+5)))))+(8*V+9) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v {S with R := Function.update S.R (Fin.castAdd tapeCount inputPort) outputs.reverse.flatten})+depth+
        (3*(28*V+33)+2*reverseCopyRowsCost batch.records.length ((2^b)*L*batch.W)+((2*(6*(2^(a+b)*(L*batch.W))+4*(batch.records.length*((2^b)*(L*batch.W)))+4*(L*batch.W)+9*(a+b)+14)+
          (40*(2^a*(2^b*(L*batch.W)))+38+restoringStockAllowance hstates a b (L*batch.W) V))+
          (mnProgPush (prepareReplicaPublicationPages (P := Empty) (Q := Q) (A := prime+K) (U := U))*
            prepareReplicaPublicationPagesCost V s g.length batch.W g.indices.length+2*(replicaPublicationCost (2^b) s (2^a-batch.records.length) g.length batch.W+6*(2^b)+6))))) depth
        (embProg (publicationPlacement inputPort outputPort) Empty.elim (.seq (chirpBankLoad publicationGeometryBank input loadWidth loadZero)
          (.seq (.seq (.seq (reverseCopyRows copyCount copySavedCount copyWidth numericalPort archive (extra 1) copySaved copyTmp)
          (uclear numericalPort)) (.seq (.seq (ownedPrefixPadding exponent packet (extra 1) pad tmp saved (pairSym (prime+K) false false))
          (program hstates))
          (.seq (embProg publicationPageBank Empty.elim (prepareReplicaPublicationPages (P := Empty)))
            (.seq (restoringReplicaPublication clock clockSave padRows wordWidth retireCount (publicationPageBank 92) savedControl gap (publicationPageBank 103) (extra 1) ambientPort acc trash pubTmp lineRows outAcc pubSaved)
              (clearWords [publicationPageBank 103,publicationPageBank 92]))))) (clearWords (inputTableWords publicationGeometryBank)))))
        (mk v {S with R := Function.update S.R (Fin.castAdd tapeCount inputPort) outputs.reverse.flatten}) n
        (mk v' {S with R := (Function.update S.R (Fin.castAdd tapeCount outputPort)
          ((List.ofFn fun j => g.output batch.W hw (rows.classRows g hkeys j) (ambient j)).flatten++outputTail))}) := by
  simpa only [publicationPlacement_numerical,publicationPlacement_ambient] using
    placed_publish_outputs_exec_within body (publicationPlacement inputPort outputPort)
      (publicationPlacement_injective inputPort outputPort hports)
      hstates a b L V batch outputs hgood copyCount copySavedCount copyWidth numericalPort archive copySaved copyTmp hcopyReg
      g hkeys hcoreWidth hw hlength hw1 hpacket hbits hfit hA exponent packet pad tmp saved hpadReg hcapacity depth
      ambient hambient publicationPageBank publicationPageBank_injective publicationPageBank_off_payload
      clock clockSave padRows wordWidth retireCount savedControl gap ambientPort acc trash pubTmp lineRows outAcc pubSaved
      hreg outputTail publicationGeometryBank publicationGeometryBank_injective input loadWidth loadZero hloadWidth hloadZero hloadInput
      (fun r => (publicationGeometryBank_off_ports r).1) (fun r => (publicationGeometryBank_off_ports r).2) hreadOff
      value hinputFit (fun i => publicationGeometryBank_variables i) hvalues publicationGeometryBank_width
      v S hnumericalBlank htableBlank hwLoad hzLoad hsrcLoad

end
end PackedTranspose
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
