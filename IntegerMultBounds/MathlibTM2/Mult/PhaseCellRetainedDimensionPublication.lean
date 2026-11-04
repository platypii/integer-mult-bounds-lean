module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedClassPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationDimensionSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedClassScatter
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOwnedPrefixPaddingStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedArchiveTileData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientPaddingData

/-! Retained unary masters supply the working publication dimensions.
Setup, computed publication and header retirement are one actual trace. -/
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
variable {Q K s t width : ℕ} [NeZero s] [NeZero t] {P U : Type}

theorem retained_dimensions_publish_class_exec_within (body : P → Pr P tapeCount Q (prime+K) U)
    (hstates : FixedStreamedBank.stateCount ≤ Q) (a b L V : ℕ)
    (batch : PackedExactBatch (prime+K) s t (2^b) L) (rows : batch.Rows)
    (g : CorePublicationClass s width) (hkeys : batch.records.map (fun r => r.k) = g.indices)
    (hcoreWidth : ∀ r ∈ batch.records, r.coreWidth = width) (hw : 0 < width)
    (hlength : L = g.length) (hw1 : 1 ≤ batch.W)
    (hpacket : 0 < L*batch.W) (hbits : a+b < V) (hfit : (L*batch.W)*2^(a+b) < 2^V) (hA : 4 ≤ prime+K)
    (d : PublicationDimensionReg → Fin tapeCount) (hd : Function.Injective d)
    (pad tmp saved : Fin tapeCount)
    (hpadReg : [(d .exponent),(d .packet),extra 1,pad,tmp,saved].Nodup)
    (hcapacity : batch.records.length ≤ 2^a) (depth : ℕ)
    (ambient : Fin (2^b) → List (Fin (prime+K+4))) (hambient : ∀ j, (ambient j).length = s*batch.W)
    (e : Fin 117 → Fin tapeCount) (he : Function.Injective e) (hoff : ∀ i, e i ≠ extra 1)
    (clockSave wordWidth retireCount savedControl gap dst acc trash pubTmp lineRows outAcc pubSaved : Fin tapeCount)
    (hreg : [(d .clock),clockSave,(d .padding),wordWidth,retireCount,(e 92),savedControl,gap,(e 103),extra 1,dst,acc,trash,pubTmp,lineRows,outAcc,pubSaved].Nodup)
    (outputTail : List (Fin (prime+K+4)))
    (v : HS tapeCount Q (prime+K) U) (S : Stacks tapeCount (prime+K))
    (hda : (S.R (d .a)).length = a) (hdb : (S.R (d .b)).length = b)
    (hdcore : (S.R (d .coreLength)).length = L) (hdword : (S.R (d .wordWidth)).length = batch.W)
    (hdrows : (S.R (d .rowCount)).length = batch.records.length)
    (hdcapacity : (S.R (d .capacity)).length = 2^a) (hdreplicas : (S.R (d .replicas)).length = 2^b)
    (hdfresh : ∀ r ∈ [PublicationDimensionReg.exponent,.packet,.padding,.missing,.saved,.tmp,.clock], S.R (d r) = [])
    (hdoff : ∀ r ∈ PublicationDimensionReg.outputs, d r ≠ extra 1 ∧ d r ≠ dst) :
    let M := PublicationDimensionReg.loaded d a b L batch.W batch.records.length (2^a) (2^b) S
    ∀ (_ : M.R pad = []) (_ : M.R tmp = []) (_ : M.R saved = [])
    (_ : M.R (base (callerGenerator 97)) = binSyms V a)
    (_ : M.R (base (callerGenerator 98)) = binSyms V b)
    (_ : M.R (base (callerGenerator 102)) = binSyms V (L*batch.W))
    (_ : M.R (base (callerGenerator 106)) = [])
    (_ : (M.R (base (callerGenerator 115))).length = V)
    (_ : ∀ r, M.R (base (callerGenerator (originReg r))) = [])
    (_ : M.R (base (callerGenerator 116)) = []) (_ : ∀ i, M.L i = [])
    (_ : ∀ i, i ≠ workerReg (reg pay) → i ≠ FixedStreamedBank.control 7 → M.R (base (callerWorker i)) = [])
    (_ : M.R (extra 1) =
      (List.ofFn fun i => (List.ofFn fun j => cstream (prime+K) batch.W (rows.values i j)).flatten).flatten)
    (_ : M.R (extra 4) = [])
    (_ : ∀ i ∈ [planeReg false,planeReg true,extra 2,extra 3,extra 5,extra 6], M.R i = [])
    (_ : M.R dst = (List.ofFn ambient).flatten++outputTail)
    (_ : M.R clockSave = [])
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
    ∃ v' n, v'.user = v.user ∧
      n ≤ (PublicationDimensionReg.timeCost a b L batch.W batch.records.length (2^a) (2^b)+(((6*(2^(a+b)*(L*batch.W))+4*(M.R (extra 1)).length+4*(L*batch.W)+9*(a+b)+14)+
        (26*(2^a*(2^b*(L*batch.W)))+24+2*restoringTimeCost hstates a b (L*batch.W) V))+
        ((prepareReplicaPublicationPagesCost V s g.length batch.W g.indices.length+
          (replicaPublicationCost (2^b) s (2^a-batch.records.length) g.length batch.W+6*(2^b)+6))+
          (2*(g.length*batch.W+(gatherControls (prime+K) ((coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).gaps batch.W)).length)+5))))+(2*((a+b)+L*batch.W+(2^b)+((2^a)-batch.records.length)*L)+9) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (2*PublicationDimensionReg.timeCost a b L batch.W batch.records.length (2^a) (2^b)+((2*(6*(2^(a+b)*(L*batch.W))+4*(M.R (extra 1)).length+4*(L*batch.W)+9*(a+b)+14)+
          (40*(2^a*(2^b*(L*batch.W)))+38+restoringStockAllowance hstates a b (L*batch.W) V))+
          (mnProgPush (prepareReplicaPublicationPages (P := Empty) (Q := Q) (A := prime+K) (U := U))*
            prepareReplicaPublicationPagesCost V s g.length batch.W g.indices.length+2*(replicaPublicationCost (2^b) s (2^a-batch.records.length) g.length batch.W+6*(2^b)+6))))) depth
        (.seq (PublicationDimensionReg.program d)
          (.seq (.seq (.seq (ownedPrefixPadding (d .exponent) (d .packet) (extra 1) pad tmp saved (pairSym (prime+K) false false))
          (program hstates))
          (.seq (embProg e Empty.elim (prepareReplicaPublicationPages (P := Empty)))
            (.seq (restoringReplicaPublication (d .clock) clockSave (d .padding) wordWidth retireCount (e 92) savedControl gap (e 103) (extra 1) dst acc trash pubTmp lineRows outAcc pubSaved)
              (clearWords [e 103,e 92])))) (clearWords (PublicationDimensionReg.outputs.map d))))
        (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R (extra 1) []) dst
          ((List.ofFn fun j => g.output batch.W hw (rows.classRows g hkeys j) (ambient j)).flatten++outputTail))}) := by
  dsimp only
  intro hpad htmp hsaved ha hb hseed hz hwidth hblank hstageCount hL hfresh hsrc hcount hcodec
    hdst hclockSave hwordWidth hlineRows hwV hsV hvolume originTail hV hpageWidth hpageLength hOrigins
    hpageCount hpageBlank hpageFresh hclean houtAcc
  let M := PublicationDimensionReg.loaded d a b L batch.W batch.records.length (2^a) (2^b) S
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := PublicationDimensionReg.exec_within body d hd a b L batch.W
    batch.records.length (2^a) (2^b) v S hda hdb hdcore hdword hdrows hdcapacity hdreplicas hdfresh depth
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := publish_class_exec_within body hstates a b L V batch rows g hkeys hcoreWidth
    hw hlength hw1 hpacket hbits hfit hA (d .exponent) (d .packet) pad tmp saved hpadReg hcapacity depth
    ambient hambient e he hoff (d .clock) clockSave (d .padding) wordWidth retireCount savedControl gap dst acc trash pubTmp lineRows outAcc pubSaved
    hreg outputTail v₁ M
    (by simp [M,PublicationDimensionReg.loaded,hd.eq_iff])
    (by simp [M,PublicationDimensionReg.loaded,hd.eq_iff]) hpad htmp hsaved
    ha hb hseed hz hwidth hblank hstageCount hL hfresh hsrc hcount hcodec hdst
    (by simp [M,PublicationDimensionReg.loaded,hd.eq_iff]) hclockSave
    (by simp [M,PublicationDimensionReg.loaded,hlength])
    hwordWidth hlineRows hwV hsV hvolume originTail hV hpageWidth hpageLength hOrigins hpageCount
    hpageBlank hpageFresh hclean houtAcc
  let ys := (List.ofFn fun j => g.output batch.W hw (rows.classRows g hkeys j) (ambient j)).flatten++outputTail
  let F : Stacks tapeCount (prime+K) := {M with R := (Function.update (Function.update M.R (extra 1) []) dst ys)}
  have hleft : (fun _ => ([] : List (Fin (prime+K+4)))) = M.L := (funext hL).symm
  have hpubeq : {M with L := (fun _ => []), R := (Function.update (Function.update M.R (extra 1) []) dst ys)} = F := by
    rw [hleft]
  change ExecWithin _ _ _ _ _ _ (mk v₂ {M with L := (fun _ => []), R := (Function.update (Function.update M.R (extra 1) []) dst ys)}) at he₂
  rw [hpubeq] at he₂
  obtain ⟨v₃,hu₃,he₃⟩ := PublicationDimensionReg.retire_exec_within body d hd a b L batch.W
    batch.records.length (2^a) (2^b) (extra 1) dst hdoff [] ys v₂ S
    (by
      intro r hr
      simp only [PublicationDimensionReg.outputs,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      all_goals exact hdfresh _ (by simp)) depth
  have hwhole := mn_seq_within_add he₁ (mn_seq_within_add he₂ he₃)
  refine ⟨v₃,n₁+(n₂+(2*((a+b)+L*batch.W+(2^b)+((2^a)-batch.records.length)*L)+9)),
    hu₃.trans (hu₂.trans hu₁),?_,?_⟩
  · simpa only [Nat.add_assoc] using Nat.add_le_add_right (Nat.add_le_add hn₁ hn₂)
      (2*((a+b)+L*batch.W+(2^b)+((2^a)-batch.records.length)*L)+9)
  · simpa only [Nat.add_zero,Nat.add_assoc,M,ys] using hwhole

end
end PackedTranspose
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
