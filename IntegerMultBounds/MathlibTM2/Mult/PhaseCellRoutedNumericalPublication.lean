module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedClassPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedRoutedClassOutput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedClassScatter
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOwnedPrefixPaddingStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedArchiveTileData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientPaddingData

/-! Consume the actual numerical prefix into ordered rows and run the existing
padding/transpose/scatter lifecycle. The numerical suffix is restored exactly;
export and publication share their peak workspace rather than summing it. -/
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

theorem routed_publish_outputs_exec_within (body : P → Pr P tapeCount Q (prime+K) U)
    (hstates : FixedStreamedBank.stateCount ≤ Q) (a b L V : ℕ)
    (batch : PackedExactBatch (prime+K) s t (2^b) L)
    (outputs : List (List (Fin (prime+K+4))))
    (hgood : List.Forall₂ PackedNormalizedJob.output batch.records outputs)
    (numerical : Fin tapeCount)
    (exportCount exportReplicas exportPacket exportClock exportVolume exportSaved exportTmp : Fin tapeCount)
    (hexportReg : [exportCount,exportReplicas,exportPacket,exportClock,exportVolume,
      numerical,extra 1,exportSaved,exportTmp].Nodup)
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
    (hnumericalDst : numerical ≠ dst)
    (outputTail : List (Fin (prime+K+4)))
    (v : HS tapeCount Q (prime+K) U) (S : Stacks tapeCount (prime+K))
    (hexponent : (S.R exponent).length = a+b) (hpacketWidth : (S.R packet).length = L*batch.W)
    (hpad : S.R pad = []) (htmp : S.R tmp = []) (hsaved : S.R saved = [])
    (ha : S.R (base (callerGenerator 97)) = binSyms V a)
    (hb : S.R (base (callerGenerator 98)) = binSyms V b)
    (hseed : S.R (base (callerGenerator 102)) = binSyms V (L*batch.W))
    (hz : S.R (base (callerGenerator 106)) = [])
    (hwidth : (S.R (base (callerGenerator 115))).length = V)
    (hblank : ∀ r, S.R (base (callerGenerator (originReg r))) = [])
    (hstageCount : S.R (base (callerGenerator 116)) = []) (hL : ∀ i, S.L i = [])
    (hfresh : ∀ i, i ≠ workerReg (reg pay) → i ≠ FixedStreamedBank.control 7 → S.R (base (callerWorker i)) = [])
    (hsourceBlank : S.R (extra 1) = [])
    (hexportReplicas : (S.R exportReplicas).length = 2^b)
    (hexportPacket : (S.R exportPacket).length = L*batch.W)
    (hexportCount : (S.R exportCount).length = batch.records.length)
    (hexportFresh : ∀ i ∈ [exportClock,exportVolume,exportSaved,exportTmp], S.R i = [])
    (hcount : S.R (extra 4) = [])
    (hcodec : ∀ i ∈ [planeReg false,planeReg true,extra 2,extra 3,extra 5,extra 6], S.R i = [])
    (hdst : S.R dst = (List.ofFn ambient).flatten++outputTail)
    (hclock : (S.R clock).length = 2^b) (hclockSave : S.R clockSave = [])
    (hpadRows : (S.R padRows).length = (2^a-batch.records.length)*g.length)
    (hwordWidth : (S.R wordWidth).length = batch.W) (hlineRows : (S.R lineRows).length = s)
    (hwV : batch.W < 2^V) (hsV : s < 2^V) (hvolume : s*batch.W < 2^V)
    (originTail : List (Fin (prime+K+4)))
    (hV : (S.R (e 115)).length = V) (hpageWidth : (S.R (e 94)).length = batch.W)
    (hpageLength : (S.R (e 102)).length = g.length)
    (hOrigins : S.R (e 109) =
      (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).origins.flatMap (binSyms V)++originTail)
    (hpageCount : S.R (e 116) = List.replicate
      (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).origins.length tick)
    (hpageBlank : ∀ i : Fin 117, i.val < 19 → S.R (e i) = [])
    (hpageFresh : ∀ i ∈ [(88 : Fin 117),89,90,91,92,103,104,105,106,107], S.R (e i) = [])
    (hclean : ∀ i ∈ [retireCount,savedControl,gap,acc,trash,pubTmp,pubSaved], S.R i = [])
    (houtAcc : S.R outAcc = []) :
    ∃ rows : batch.Rows, ∃ v' n, v'.user = v.user ∧
      n ≤ (PackedExactBatch.generatedExportCost batch.records.length (2^b) (L*batch.W))+(((6*(2^(a+b)*(L*batch.W))+4*(batch.records.length*((2^b)*(L*batch.W)))+4*(L*batch.W)+9*(a+b)+14)+
        (26*(2^a*(2^b*(L*batch.W)))+24+2*restoringTimeCost hstates a b (L*batch.W) V))+
        ((prepareReplicaPublicationPagesCost V s g.length batch.W g.indices.length+
          (replicaPublicationCost (2^b) s (2^a-batch.records.length) g.length batch.W+6*(2^b)+6))+
          (2*(g.length*batch.W+(gatherControls (prime+K) ((coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).gaps batch.W)).length)+5))) ∧
      let lines := fun j => g.output batch.W hw (rows.classRows g hkeys j) (ambient j)
      let result : Stacks tapeCount (prime+K) := {S with R := (Function.update S.R dst
        ((List.ofFn lines).flatten++outputTail))}
      mnSize (mk v' result) ≤ mnSize (mk v {S with R := (Function.update S.R numerical
        (outputs.reverse.flatten++S.R numerical))}) ∧
      result.R numerical = S.R numerical ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v {S with R := Function.update S.R numerical (outputs.reverse.flatten++S.R numerical)})+depth+
        (max (2*PackedExactBatch.generatedExportCost batch.records.length (2^b) (L*batch.W)) ((2*(6*(2^(a+b)*(L*batch.W))+4*(batch.records.length*((2^b)*(L*batch.W)))+4*(L*batch.W)+9*(a+b)+14)+
          (40*(2^a*(2^b*(L*batch.W)))+38+restoringStockAllowance hstates a b (L*batch.W) V))+
          (mnProgPush (prepareReplicaPublicationPages (P := Empty) (Q := Q) (A := prime+K) (U := U))*
            prepareReplicaPublicationPagesCost V s g.length batch.W g.indices.length+2*(replicaPublicationCost (2^b) s (2^a-batch.records.length) g.length batch.W+6*(2^b)+6))))) depth
        (.seq (PackedExactBatch.generatedExport numerical exportCount exportReplicas exportPacket exportClock exportVolume (extra 1) exportSaved exportTmp) (.seq (.seq (ownedPrefixPadding exponent packet (extra 1) pad tmp saved (pairSym (prime+K) false false))
          (program hstates))
          (.seq (embProg e Empty.elim (prepareReplicaPublicationPages (P := Empty)))
            (.seq (restoringReplicaPublication clock clockSave padRows wordWidth retireCount (e 92) savedControl gap (e 103) (extra 1) dst acc trash pubTmp lineRows outAcc pubSaved)
              (clearWords [e 103,e 92])))))
        (mk v {S with R := Function.update S.R numerical (outputs.reverse.flatten++S.R numerical)}) n
        (mk v' result) ∧
      ∀ (j : Fin (2^b)) k, k ∉ g.indices → ∀ i : ZMod s, i ∈ IntegerMultBounds.NLogN.PhaseCellMatrix.ownedCore s width k →
        ((lines j).drop (i.val*batch.W)).take batch.W =
          ((ambient j).drop (i.val*batch.W)).take batch.W := by
  dsimp only
  let F : Stacks tapeCount (prime+K) := {S with R := (Function.update S.R
    numerical (outputs.reverse.flatten++S.R numerical))}
  have hc := hexportReg
  regs_ne hc
  obtain ⟨rows,v₁,n₁,hu₁,hn₁,hsize₁,he₁,hcert₁⟩ := PackedExactBatch.generatedExport_exec
    (body := body) numerical exportCount exportReplicas exportPacket exportClock exportVolume (extra 1) exportSaved exportTmp
    hexportReg batch outputs hgood (S.R numerical) v F
    (by simpa only [F,Function.update_of_ne ‹exportCount ≠ numerical›] using hexportCount)
    (by simpa only [F,Function.update_of_ne ‹exportReplicas ≠ numerical›] using hexportReplicas)
    (by simpa only [F,Function.update_of_ne ‹exportPacket ≠ numerical›] using hexportPacket)
    (by simp only [F,Function.update_self])
    (by
      intro i hi
      have hoff : i ≠ numerical := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl
        all_goals first | assumption | (apply Ne.symm; assumption)
      simpa only [F,Function.update_of_ne hoff] using hexportFresh i hi)
  let M : Stacks tapeCount (prime+K) := {S with R := Function.update S.R (extra 1) rows.stream}
  have hmove : {F with R := (Function.update (Function.update F.R numerical
      (S.R numerical)) (extra 1) (rows.stream++F.R (extra 1)))} = M := by
    simp only [F,Function.update_idem,
      Function.update_of_ne ‹numerical ≠ extra 1›.symm,
      hsourceBlank,List.append_nil,Function.update_eq_self,M]
  rw [hmove] at he₁ hsize₁ hcert₁
  have hstable (i : Fin tapeCount) (hi : i ≠ extra 1) : M.R i = S.R i := by simp only [M,Function.update_of_ne hi]
  have hp := hpadReg
  regs_ne hp
  have hr := hreg
  regs_ne hr
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := publish_class_exec_within body hstates a b L V batch rows g hkeys hcoreWidth
    hw hlength hw1 hpacket hbits hfit hA exponent packet pad tmp saved hpadReg hcapacity depth
    ambient hambient e he hoff clock clockSave padRows wordWidth retireCount savedControl gap dst acc trash pubTmp lineRows outAcc pubSaved
    hreg outputTail v₁ M
    (by rw [hstable _ ‹exponent ≠ extra 1›]; exact hexponent)
    (by rw [hstable _ ‹packet ≠ extra 1›]; exact hpacketWidth)
    (by rw [hstable _ ‹extra 1 ≠ pad›.symm]; exact hpad)
    (by rw [hstable _ ‹extra 1 ≠ tmp›.symm]; exact htmp)
    (by rw [hstable _ ‹extra 1 ≠ saved›.symm]; exact hsaved)
    (by rw [hstable _ (base_extra _ _)]; exact ha)
    (by rw [hstable _ (base_extra _ _)]; exact hb)
    (by rw [hstable _ (base_extra _ _)]; exact hseed)
    (by rw [hstable _ (base_extra _ _)]; exact hz)
    (by rw [hstable _ (base_extra _ _)]; exact hwidth)
    (by intro r; rw [hstable _ (base_extra _ _)]; exact hblank r)
    (by rw [hstable _ (base_extra _ _)]; exact hstageCount) hL
    (by intro i hi hj; rw [hstable _ (base_extra _ _)]; exact hfresh i hi hj)
    (by simp only [M,Function.update_self,PackedExactBatch.Rows.stream])
    (by rw [hstable _ (by simp [extra,Fin.ext_iff])]; exact hcount)
    (by
      intro i hi
      have hc := codec_registers
      regs_ne hc
      have ho : i ≠ extra 1 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | assumption | (apply Ne.symm; assumption)
      rw [hstable _ ho]
      exact hcodec i hi)
    (by rw [hstable _ ‹extra 1 ≠ dst›.symm]; exact hdst)
    (by rw [hstable _ ‹clock ≠ extra 1›]; exact hclock)
    (by rw [hstable _ ‹clockSave ≠ extra 1›]; exact hclockSave)
    (by rw [hstable _ ‹padRows ≠ extra 1›]; exact hpadRows)
    (by rw [hstable _ ‹wordWidth ≠ extra 1›]; exact hwordWidth)
    (by rw [hstable _ ‹extra 1 ≠ lineRows›.symm]; exact hlineRows)
    hwV hsV hvolume originTail
    (by rw [hstable _ (hoff _)]; exact hV)
    (by rw [hstable _ (hoff _)]; exact hpageWidth)
    (by rw [hstable _ (hoff _)]; exact hpageLength)
    (by rw [hstable _ (hoff _)]; exact hOrigins)
    (by rw [hstable _ (hoff _)]; exact hpageCount)
    (by intro i hi; rw [hstable _ (hoff _)]; exact hpageBlank i hi)
    (by intro i hi; rw [hstable _ (hoff _)]; exact hpageFresh i hi)
    (by
      intro i hi
      have ho : i ≠ extra 1 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | assumption | (apply Ne.symm; assumption)
      rw [hstable _ ho]
      exact hclean i hi)
    (by rw [hstable _ ‹extra 1 ≠ outAcc›.symm]; exact houtAcc)
  have hvol : (M.R (extra 1)).length = batch.records.length*((2^b)*(L*batch.W)) := by
    simp only [M,Function.update_self,PackedExactBatch.Rows.stream_length]
  rw [hvol] at hn₂ he₂
  let ys := (List.ofFn fun j => g.output batch.W hw (rows.classRows g hkeys j) (ambient j)).flatten++outputTail
  have hend : {M with L := (fun _ => []), R := (Function.update (Function.update M.R (extra 1) []) dst ys)} =
      {S with R := Function.update S.R dst ys} := by
    have hl : (fun _ => ([] : List (Fin (prime+K+4)))) = S.L := (funext hL).symm
    simp only [M,Function.update_idem,hl]
    rw [←hsourceBlank,Function.update_eq_self]
  change ExecWithin _ _ _ _ _ _ (mk v₂ {M with L := (fun _ => []), R := (Function.update (Function.update M.R (extra 1) []) dst ys)}) at he₂
  rw [hend] at he₂
  have hys : ys.length = (S.R dst).length := by
    have hline (j : Fin (2^b)) :
        (g.output batch.W hw (rows.classRows g hkeys j) (ambient j)).length = s*batch.W :=
      g.output_length batch.W hw _ (rows.classRows_length g hkeys hcoreWidth j) _ (hambient j)
    rw [hdst]
    simp only [ys,List.length_append]
    congr 1
    rw [length_flatten_const _ (by
      intro line hmem
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hmem
      exact hline j),length_flatten_const _ (by
      intro line hline
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hline
      exact hambient j),List.length_ofFn,List.length_ofFn]
  have hafter : mnSize (mk v₂ {S with R := Function.update S.R dst ys}) = mnSize (mk v S) := by
    have hb : mnSize (mk v₂ {S with R := Function.update S.R dst ys})+(S.R dst).length =
        mnSize (mk v S)+ys.length := by
      simpa only [mk,update_rt,get_rt] using mn_size_update (mk v S) v₂ (.rt dst) ys
    rw [hys] at hb
    omega
  have hbefore : mnSize (mk v F) = mnSize (mk v S)+outputs.reverse.flatten.length := by
    have hb : mnSize (mk v F)+(S.R numerical).length =
        mnSize (mk v S)+(outputs.reverse.flatten++S.R numerical).length := by
      simpa only [F,mk,update_rt,get_rt] using
        mn_size_update (mk v S) v (.rt numerical) (outputs.reverse.flatten++S.R numerical)
    simp only [List.length_append] at hb
    omega
  refine ⟨rows,v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,?_,?_,?_,?_⟩
  · change mnSize (mk v₂ {S with R := Function.update S.R dst ys}) ≤ mnSize (mk v F)
    omega
  · exact Function.update_of_ne hnumericalDst _ _
  · exact mn_seq_within_max (le_of_eq hsize₁) (hcert₁ depth) he₂
  · intro j k hk i hi
    simpa only [PackedExactBatch.Rows.publicationReplica_output] using
      rows.publicationReplica_word_preserves g hkeys hcoreWidth hw
        (C := 0) (fun i _ => Fin.elim0 i) ambient hambient j k hk i hi

end
end PackedTranspose
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
