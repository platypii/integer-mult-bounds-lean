module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeometryLoadedNumericalPublication
public import IntegerMultBounds.MathlibTM2.Host.EmbedInputOutputStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputTableUpdate
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputTableRetirement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedOutputPublicationCopy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedClassScatter
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOwnedPrefixPaddingStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedArchiveTileData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientPaddingData

/-! Place geometry-loading numerical publication in a larger selected caller.
Actual retained binary masters supply router geometry; spectator stock is counted once. -/
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

theorem placed_publish_outputs_exec_within (body : P → Pr P T Q (prime+K) U)
    (placement : Fin tapeCount → Fin T) (hplacement : Function.Injective placement)
    (hstates : FixedStreamedBank.stateCount ≤ Q) (a b L V : ℕ)
    (batch : PackedExactBatch (prime+K) s t (2^b) L)
    (outputs : List (List (Fin (prime+K+4))))
    (hgood : List.Forall₂ PackedNormalizedJob.output batch.records outputs)
    (copyReplicas copyPacket copyCount copySavedCount copyWidth numerical archive copySaved copyTmp : Fin tapeCount)
    (hcopyReg : [copyReplicas,copyPacket,copyCount,copySavedCount,copyWidth,numerical,archive,extra 1,copySaved,copyTmp].Nodup)
    (g : CorePublicationClass s width) (hkeys : batch.records.map (fun r => r.k) = g.indices)
    (hcoreWidth : ∀ r ∈ batch.records, r.coreWidth = width) (hw : 0 < width)
    (hlength : L = g.length) (hw1 : 1 ≤ batch.W)
    (hpacket : 0 < L*batch.W) (hbits : a+b < V) (hfit : (L*batch.W)*2^(a+b) < 2^V) (hA : 4 ≤ prime+K)
    (exponent packet pad tmp saved : Fin tapeCount)
    (hpadReg : [exponent,packet,extra 1,pad,tmp,saved].Nodup)
    (hcapacity : batch.records.length ≤ 2^a) (depth : ℕ)
    (ambient : Fin (2^b) → List (Fin (prime+K+4))) (hambient : ∀ j, (ambient j).length = s*batch.W)
    (e : Fin 117 → Fin tapeCount) (he : Function.Injective e) (hoff : ∀ i, e i ≠ extra 1)
    (clock clockSave padRows wordWidth retireCount savedControl gap dst acc trash pubTmp lineRows outAcc pubSaved : Fin tapeCount)
    (hreg : [clock,clockSave,padRows,wordWidth,retireCount,(e 92),savedControl,gap,(e 103),extra 1,dst,acc,trash,pubTmp,lineRows,outAcc,pubSaved].Nodup)
    (outputTail : List (Fin (prime+K+4)))
    (rg : TblR 3 → Fin tapeCount) (hrg : Function.Injective rg) (input : Fin 3 → Fin tapeCount)
    (loadWidth loadZero : Fin tapeCount)
    (hloadWidth : ∀ r, rg r ≠ loadWidth) (hloadZero : ∀ r, rg r ≠ loadZero)
    (hloadInput : ∀ i r, rg r ≠ input i)
    (htableNumerical : ∀ r, rg r ≠ numerical) (htableDst : ∀ r, rg r ≠ dst)
    (hreadOff : loadWidth ≠ numerical ∧ loadZero ≠ numerical ∧ ∀ i, input i ≠ numerical)
    (value : Fin tapeCount → ℕ) (hinputFit : ∀ i, value (input i) < 2^V)
    (hvars : ∀ i, rg (.v i) = ![base (callerGenerator 97),base (callerGenerator 98),base (callerGenerator 102)] i)
    (hvalues : ∀ i, value (input i) = ![a,b,L*batch.W] i)
    (hwr : rg .wr = base (callerGenerator 115))
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hnumericalBlank : (embStk placement S).R numerical = [])
    (htableBlank : ∀ r, (embStk placement S).R (rg r) = [])
    (hwLoad : ((embStk placement S).R loadWidth).length = V)
    (hzLoad : (embStk placement S).R loadZero = [])
    (hsrcLoad : ∀ i, (embStk placement S).R (input i) = binSyms V (value (input i))) :
    let M := loadedInputTable rg input V value (embStk placement S)
    ∀ (_ : (M.R exponent).length = a+b) (_ : (M.R packet).length = L*batch.W)
    (_ : M.R pad = []) (_ : M.R tmp = []) (_ : M.R saved = [])
    (_ : M.R (base (callerGenerator 106)) = [])
    (_ : ∀ r, M.R (base (callerGenerator (originReg r))) = [])
    (_ : M.R (base (callerGenerator 116)) = []) (_ : ∀ i, M.L i = [])
    (_ : ∀ i, i ≠ workerReg (reg pay) → i ≠ FixedStreamedBank.control 7 → M.R (base (callerWorker i)) = [])
    (_ : M.R (extra 1) = [])
    (_ : (M.R copyReplicas).length = 2^b) (_ : (M.R copyPacket).length = L*batch.W)
    (_ : (M.R copyCount).length = batch.records.length)
    (_ : M.R copyWidth = [])
    (_ : ∀ i ∈ [copySavedCount,archive,copySaved,copyTmp], M.R i = [])
    (_ : M.R (extra 4) = [])
    (_ : ∀ i ∈ [planeReg false,planeReg true,extra 2,extra 3,extra 5,extra 6], M.R i = [])
    (_ : M.R dst = (List.ofFn ambient).flatten++outputTail)
    (_ : (M.R clock).length = 2^b) (_ : M.R clockSave = [])
    (_ : (M.R padRows).length = (2^a-batch.records.length)*g.length)
    (_ : (M.R wordWidth).length = batch.W) (_ : (M.R lineRows).length = s)
    (_ : batch.W < 2^V) (_ : s < 2^V) (_ : s*batch.W < 2^V)
    (originTail : List (Fin (prime+K+4)))
    (_ : (M.R (e 115)).length = V) (_ : (M.R (e 94)).length = batch.W)
    (_ : (M.R (e 102)).length = g.length)
    (_ : M.R (e 109) =
      (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).origins.flatMap (binSyms V)++originTail)
    (_ : M.R (e 116) = List.replicate
      (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).origins.length tick)
    (_ : ∀ i : Fin 117, i.val < 19 → M.R (e i) = [])
    (_ : ∀ i ∈ [(88 : Fin 117),89,90,91,92,103,104,105,106,107], M.R (e i) = [])
    (_ : ∀ i ∈ [retireCount,savedControl,gap,acc,trash,pubTmp,pubSaved], M.R i = [])
    (_ : M.R outAcc = []),
    ∃ rows : batch.Rows, ∃ v' n, v'.user = v.user ∧
      n ≤ ((28*V+33)+((PackedExactBatch.generatedOutputCopyTimeCost batch.records.length (2^b) L batch.W outputs.reverse.flatten.length)+(((6*(2^(a+b)*(L*batch.W))+4*(batch.records.length*((2^b)*(L*batch.W)))+4*(L*batch.W)+9*(a+b)+14)+
        (26*(2^a*(2^b*(L*batch.W)))+24+2*restoringTimeCost hstates a b (L*batch.W) V))+
        ((prepareReplicaPublicationPagesCost V s g.length batch.W g.indices.length+
          (replicaPublicationCost (2^b) s (2^a-batch.records.length) g.length batch.W+6*(2^b)+6))+
          (2*(g.length*batch.W+(gatherControls (prime+K) ((coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).gaps batch.W)).length)+5)))))+(8*V+9) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v {S with R := Function.update S.R (placement numerical) outputs.reverse.flatten})+depth+
        (3*(28*V+33)+PackedExactBatch.generatedOutputCopyStock batch.records.length (2^b) L batch.W+((2*(6*(2^(a+b)*(L*batch.W))+4*(batch.records.length*((2^b)*(L*batch.W)))+4*(L*batch.W)+9*(a+b)+14)+
          (40*(2^a*(2^b*(L*batch.W)))+38+restoringStockAllowance hstates a b (L*batch.W) V))+
          (mnProgPush (prepareReplicaPublicationPages (P := Empty) (Q := Q) (A := prime+K) (U := U))*
            prepareReplicaPublicationPagesCost V s g.length batch.W g.indices.length+2*(replicaPublicationCost (2^b) s (2^a-batch.records.length) g.length batch.W+6*(2^b)+6))))) depth
        (embProg placement Empty.elim (.seq (chirpBankLoad rg input loadWidth loadZero)
          (.seq (.seq (PackedExactBatch.generatedOutputCopyProgram copyReplicas copyPacket copyCount copySavedCount copyWidth numerical archive (extra 1) copySaved copyTmp) (.seq (.seq (ownedPrefixPadding exponent packet (extra 1) pad tmp saved (pairSym (prime+K) false false))
          (program hstates))
          (.seq (embProg e Empty.elim (prepareReplicaPublicationPages (P := Empty)))
            (.seq (restoringReplicaPublication clock clockSave padRows wordWidth retireCount (e 92) savedControl gap (e 103) (extra 1) dst acc trash pubTmp lineRows outAcc pubSaved)
              (clearWords [e 103,e 92]))))) (clearWords (inputTableWords rg)))))
        (mk v {S with R := Function.update S.R (placement numerical) outputs.reverse.flatten}) n
        (mk v' {S with R := (Function.update S.R (placement dst)
          ((List.ofFn fun j => g.output batch.W hw (rows.classRows g hkeys j) (ambient j)).flatten++outputTail))}) := by
  dsimp only
  intro hexponent hpacketWidth hpad htmp hsaved hz hblank hstageCount hL hfresh hsourceBlank hcopyReplicas hcopyPacket hcopyCount hcopyBlank hcopyFresh hcount hcodec hdst hclock hclockSave hpadRows hwordWidth hlineRows hwV hsV hvolume originTail hV hpageWidth hpageLength hOrigins hpageCount hpageBlank hpageFresh hclean houtAcc
  obtain ⟨rows,vi,n,hu,hn,hex⟩ := geometry_loaded_publish_outputs_exec_within (fun p : Empty => nomatch p)
    hstates a b L V batch outputs hgood copyReplicas copyPacket copyCount copySavedCount copyWidth numerical archive copySaved copyTmp hcopyReg
    g hkeys hcoreWidth hw hlength hw1 hpacket hbits hfit hA exponent packet pad tmp saved hpadReg hcapacity depth
    ambient hambient e he hoff clock clockSave padRows wordWidth retireCount savedControl gap dst acc trash pubTmp lineRows outAcc pubSaved
    hreg outputTail rg hrg input loadWidth loadZero hloadWidth hloadZero hloadInput htableNumerical htableDst hreadOff
    value hinputFit hvars hvalues hwr (embDn placement v) (embStk placement S)
    hnumericalBlank htableBlank hwLoad hzLoad hsrcLoad hexponent hpacketWidth hpad htmp hsaved hz hblank hstageCount hL hfresh hsourceBlank hcopyReplicas hcopyPacket hcopyCount hcopyBlank hcopyFresh hcount hcodec hdst hclock hclockSave hpadRows hwordWidth hlineRows hwV hsV hvolume originTail hV hpageWidth hpageLength hOrigins hpageCount hpageBlank hpageFresh hclean houtAcc
  let ys := (List.ofFn fun j => g.output batch.W hw (rows.classRows g hkeys j) (ambient j)).flatten++outputTail
  obtain ⟨v',hu',ht⟩ := exec_emb_input_output_within placement hplacement (body' := body) (ι := Empty.elim)
    (fun p : Empty => nomatch p) numerical dst outputs.reverse.flatten ys v S hex
  exact ⟨rows,v',n,hu'.trans hu,hn,ht⟩

end
end PackedTranspose
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
