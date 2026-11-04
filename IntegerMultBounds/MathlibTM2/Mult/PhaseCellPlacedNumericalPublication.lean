module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNumericalOutputPublication
public import IntegerMultBounds.MathlibTM2.Host.EmbedInputOutputStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedOutputPublicationCopy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedClassScatter
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOwnedPrefixPaddingStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedArchiveTileData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientPaddingData

/-! Place actual numerical-output publication inside a larger selected caller.
Spectator storage is preserved and charged once through the stock embedding. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
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
    (copyCount copySavedCount copyWidth numerical archive copySaved copyTmp : Fin tapeCount)
    (hcopyReg : [copyCount,copySavedCount,copyWidth,numerical,archive,extra 1,copySaved,copyTmp].Nodup)
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
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K)) :
    let S₀ := embStk placement S
    ∀
    (_ : (S₀.R exponent).length = a+b) (_ : (S₀.R packet).length = L*batch.W)
    (_ : S₀.R pad = []) (_ : S₀.R tmp = []) (_ : S₀.R saved = [])
    (_ : S₀.R (base (callerGenerator 97)) = binSyms V a)
    (_ : S₀.R (base (callerGenerator 98)) = binSyms V b)
    (_ : S₀.R (base (callerGenerator 102)) = binSyms V (L*batch.W))
    (_ : S₀.R (base (callerGenerator 106)) = [])
    (_ : (S₀.R (base (callerGenerator 115))).length = V)
    (_ : ∀ r, S₀.R (base (callerGenerator (originReg r))) = [])
    (_ : S₀.R (base (callerGenerator 116)) = []) (_ : ∀ i, S₀.L i = [])
    (_ : ∀ i, i ≠ workerReg (reg pay) → i ≠ FixedStreamedBank.control 7 → S₀.R (base (callerWorker i)) = [])
    (_ : S₀.R (extra 1) = []) (_ : S₀.R numerical = [])
    (_ : (S₀.R copyCount).length = batch.records.length)
    (_ : (S₀.R copyWidth).length = (2^b)*L*batch.W)
    (_ : ∀ i ∈ [copySavedCount,archive,copySaved,copyTmp], S₀.R i = [])
    (_ : S₀.R (extra 4) = [])
    (_ : ∀ i ∈ [planeReg false,planeReg true,extra 2,extra 3,extra 5,extra 6], S₀.R i = [])
    (_ : S₀.R dst = (List.ofFn ambient).flatten++outputTail)
    (_ : (S₀.R clock).length = 2^b) (_ : S₀.R clockSave = [])
    (_ : (S₀.R padRows).length = (2^a-batch.records.length)*g.length)
    (_ : (S₀.R wordWidth).length = batch.W) (_ : (S₀.R lineRows).length = s)
    (_ : batch.W < 2^V) (_ : s < 2^V) (_ : s*batch.W < 2^V)
    (originTail : List (Fin (prime+K+4)))
    (_ : (S₀.R (e 115)).length = V) (_ : (S₀.R (e 94)).length = batch.W)
    (_ : (S₀.R (e 102)).length = g.length)
    (_ : S₀.R (e 109) =
      (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).origins.flatMap (binSyms V)++originTail)
    (_ : S₀.R (e 116) = List.replicate
      (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).origins.length tick)
    (_ : ∀ i : Fin 117, i.val < 19 → S₀.R (e i) = [])
    (_ : ∀ i ∈ [(88 : Fin 117),89,90,91,92,103,104,105,106,107], S₀.R (e i) = [])
    (_ : ∀ i ∈ [retireCount,savedControl,gap,acc,trash,pubTmp,pubSaved], S₀.R i = [])
    (_ : S₀.R outAcc = []),
    ∃ rows : batch.Rows, ∃ v' n, v'.user = v.user ∧
      n ≤ (reverseCopyRowsCost batch.records.length ((2^b)*L*batch.W)+2*outputs.reverse.flatten.length+2)+(((6*(2^(a+b)*(L*batch.W))+4*(batch.records.length*((2^b)*(L*batch.W)))+4*(L*batch.W)+9*(a+b)+14)+
        (26*(2^a*(2^b*(L*batch.W)))+24+2*restoringTimeCost hstates a b (L*batch.W) V))+
        ((prepareReplicaPublicationPagesCost V s g.length batch.W g.indices.length+
          (replicaPublicationCost (2^b) s (2^a-batch.records.length) g.length batch.W+6*(2^b)+6))+
          (2*(g.length*batch.W+(gatherControls (prime+K) ((coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).gaps batch.W)).length)+5))) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v {S with R := Function.update S.R (placement numerical) outputs.reverse.flatten})+depth+
        (2*reverseCopyRowsCost batch.records.length ((2^b)*L*batch.W)+((2*(6*(2^(a+b)*(L*batch.W))+4*(batch.records.length*((2^b)*(L*batch.W)))+4*(L*batch.W)+9*(a+b)+14)+
          (40*(2^a*(2^b*(L*batch.W)))+38+restoringStockAllowance hstates a b (L*batch.W) V))+
          (mnProgPush (prepareReplicaPublicationPages (P := Empty) (Q := Q) (A := prime+K) (U := U))*
            prepareReplicaPublicationPagesCost V s g.length batch.W g.indices.length+2*(replicaPublicationCost (2^b) s (2^a-batch.records.length) g.length batch.W+6*(2^b)+6))))) depth
        (embProg placement Empty.elim (.seq (.seq (reverseCopyRows copyCount copySavedCount copyWidth numerical archive (extra 1) copySaved copyTmp)
          (uclear numerical)) (.seq (.seq (ownedPrefixPadding exponent packet (extra 1) pad tmp saved (pairSym (prime+K) false false))
          (program hstates))
          (.seq (embProg e Empty.elim (prepareReplicaPublicationPages (P := Empty)))
            (.seq (restoringReplicaPublication clock clockSave padRows wordWidth retireCount (e 92) savedControl gap (e 103) (extra 1) dst acc trash pubTmp lineRows outAcc pubSaved)
              (clearWords [e 103,e 92]))))))
        (mk v {S with R := Function.update S.R (placement numerical) outputs.reverse.flatten}) n
        (mk v' {S with R := (Function.update S.R (placement dst)
          ((List.ofFn fun j => g.output batch.W hw (rows.classRows g hkeys j) (ambient j)).flatten++outputTail))}) := by
  dsimp only
  intro hexponent hpacketWidth hpad htmp hsaved ha hb hseed hz hwidth hblank hstageCount hL hfresh hsourceBlank hnumericalBlank hcopyCount hcopyWidth hcopyFresh hcount hcodec hdst hclock hclockSave hpadRows hwordWidth hlineRows hwV hsV hvolume originTail hV hpageWidth hpageLength hOrigins hpageCount hpageBlank hpageFresh hclean houtAcc
  obtain ⟨rows,vi,n,hu,hn,hex⟩ := publish_outputs_exec_within (fun p : Empty => nomatch p)
    hstates a b L V batch outputs hgood copyCount copySavedCount copyWidth numerical archive copySaved copyTmp hcopyReg
    g hkeys hcoreWidth hw hlength hw1 hpacket hbits hfit hA exponent packet pad tmp saved hpadReg hcapacity depth
    ambient hambient e he hoff clock clockSave padRows wordWidth retireCount savedControl gap dst acc trash pubTmp lineRows outAcc pubSaved
    hreg outputTail (embDn placement v) (embStk placement S)
    hexponent hpacketWidth hpad htmp hsaved ha hb hseed hz hwidth hblank hstageCount hL hfresh hsourceBlank hnumericalBlank hcopyCount hcopyWidth hcopyFresh hcount hcodec hdst hclock hclockSave hpadRows hwordWidth hlineRows hwV hsV hvolume originTail hV hpageWidth hpageLength hOrigins hpageCount hpageBlank hpageFresh hclean houtAcc
  let ys := (List.ofFn fun j => g.output batch.W hw (rows.classRows g hkeys j) (ambient j)).flatten++outputTail
  obtain ⟨v',hu',ht⟩ := exec_emb_input_output_within placement hplacement (body' := body) (ι := Empty.elim)
    (fun p : Empty => nomatch p) numerical dst outputs.reverse.flatten ys v S hex
  exact ⟨rows,v',n,hu'.trans hu,hn,ht⟩

end
end PackedTranspose
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
