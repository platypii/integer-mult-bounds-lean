module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedClassPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedOutputPublicationCopy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedClassScatter
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOwnedPrefixPaddingStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedArchiveTileData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientPaddingData

/-! Publish the actual reversed numerical result. The restoring handoff
extracts certified rows, retires the old result, and feeds the existing lifecycle. -/
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

theorem publish_outputs_exec_within (body : P → Pr P tapeCount Q (prime+K) U)
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
    (hsourceBlank : S.R (extra 1) = []) (hnumericalBlank : S.R numerical = [])
    (hcopyCount : (S.R copyCount).length = batch.records.length)
    (hcopyWidth : (S.R copyWidth).length = (2^b)*L*batch.W)
    (hcopyFresh : ∀ i ∈ [copySavedCount,archive,copySaved,copyTmp], S.R i = [])
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
      n ≤ (reverseCopyRowsCost batch.records.length ((2^b)*L*batch.W)+2*outputs.reverse.flatten.length+2)+(((6*(2^(a+b)*(L*batch.W))+4*(batch.records.length*((2^b)*(L*batch.W)))+4*(L*batch.W)+9*(a+b)+14)+
        (26*(2^a*(2^b*(L*batch.W)))+24+2*restoringTimeCost hstates a b (L*batch.W) V))+
        ((prepareReplicaPublicationPagesCost V s g.length batch.W g.indices.length+
          (replicaPublicationCost (2^b) s (2^a-batch.records.length) g.length batch.W+6*(2^b)+6))+
          (2*(g.length*batch.W+(gatherControls (prime+K) ((coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).gaps batch.W)).length)+5))) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v {S with R := Function.update S.R numerical outputs.reverse.flatten})+depth+
        (2*reverseCopyRowsCost batch.records.length ((2^b)*L*batch.W)+((2*(6*(2^(a+b)*(L*batch.W))+4*(batch.records.length*((2^b)*(L*batch.W)))+4*(L*batch.W)+9*(a+b)+14)+
          (40*(2^a*(2^b*(L*batch.W)))+38+restoringStockAllowance hstates a b (L*batch.W) V))+
          (mnProgPush (prepareReplicaPublicationPages (P := Empty) (Q := Q) (A := prime+K) (U := U))*
            prepareReplicaPublicationPagesCost V s g.length batch.W g.indices.length+2*(replicaPublicationCost (2^b) s (2^a-batch.records.length) g.length batch.W+6*(2^b)+6))))) depth
        (.seq (.seq (reverseCopyRows copyCount copySavedCount copyWidth numerical archive (extra 1) copySaved copyTmp)
          (uclear numerical)) (.seq (.seq (ownedPrefixPadding exponent packet (extra 1) pad tmp saved (pairSym (prime+K) false false))
          (program hstates))
          (.seq (embProg e Empty.elim (prepareReplicaPublicationPages (P := Empty)))
            (.seq (restoringReplicaPublication clock clockSave padRows wordWidth retireCount (e 92) savedControl gap (e 103) (extra 1) dst acc trash pubTmp lineRows outAcc pubSaved)
              (clearWords [e 103,e 92])))))
        (mk v {S with R := Function.update S.R numerical outputs.reverse.flatten}) n
        (mk v' {S with R := (Function.update S.R dst
          ((List.ofFn fun j => g.output batch.W hw (rows.classRows g hkeys j) (ambient j)).flatten++outputTail))}) := by
  let F : Stacks tapeCount (prime+K) := {S with R := Function.update S.R numerical outputs.reverse.flatten}
  have hc := hcopyReg
  regs_ne hc
  obtain ⟨rows,v₁,n₁,hu₁,hn₁,he₁⟩ := PackedExactBatch.move_outputs_for_publication_exec_within body batch outputs hgood
    copyCount copySavedCount copyWidth numerical archive (extra 1) copySaved copyTmp hcopyReg v F
    (by simpa only [F,Function.update_of_ne ‹copyCount ≠ numerical›] using hcopyCount)
    (by simpa only [F,Function.update_of_ne ‹copyWidth ≠ numerical›] using hcopyWidth)
    (by simp only [F,Function.update_self])
    (by
      intro i hi
      have hoff : i ≠ numerical := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl
        all_goals first | assumption | (apply Ne.symm; assumption)
      simpa only [F,Function.update_of_ne hoff] using hcopyFresh i hi) depth
  let M : Stacks tapeCount (prime+K) := {S with R := Function.update S.R (extra 1) rows.stream}
  have hmove : {F with R := Function.update (Function.update F.R (extra 1) (rows.stream++F.R (extra 1))) numerical []} = M := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi : i = numerical
    · subst i; simp [M,‹numerical ≠ extra 1›,hnumericalBlank]
    by_cases hj : i = extra 1
    · subst i; simp [F,M,‹numerical ≠ extra 1›.symm,hsourceBlank]
    · simp [F,M,hi,hj]
  rw [hmove] at he₁
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
  refine ⟨rows,v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,?_⟩
  simpa only [F,ys,Nat.add_assoc] using mn_seq_within_add he₁ he₂

end
end PackedTranspose
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
