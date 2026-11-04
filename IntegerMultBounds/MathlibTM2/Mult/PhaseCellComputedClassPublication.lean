module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedPublicationTranspose
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedClassScatter
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOwnedPrefixPaddingStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedArchiveTileData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientPaddingData

/-! One physical execution pads and transposes the computed class rows,
then scatters them into ambient replica lines with restored borrowed controls. -/
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

theorem publish_class_exec_within (body : P → Pr P tapeCount Q (prime+K) U)
    (hstates : FixedStreamedBank.stateCount ≤ Q) (a b L V : ℕ)
    (batch : PackedExactBatch (prime+K) s t (2^b) L) (rows : batch.Rows)
    (g : CorePublicationClass s width) (hkeys : batch.records.map (fun r => r.k) = g.indices)
    (hcoreWidth : ∀ r ∈ batch.records, r.coreWidth = width) (hw : 0 < width)
    (hlength : L = g.length) (hw1 : 1 ≤ batch.W)
    (hpacket : 0 < L*batch.W) (hbits : a+b < V) (hfit : (L*batch.W)*2^(a+b) < 2^V) (hA : 4 ≤ prime+K)
    (exponent packet pad tmp saved : Fin tapeCount)
    (hpadReg : [exponent,packet,extra 1,pad,tmp,saved].Nodup)
    (hcapacity : batch.records.length ≤ 2^a) (depth : ℕ)
    (ambient : Fin (2^b) → List (Fin (prime+K+4))) (hambient : ∀ j, (ambient j).length = s*batch.W)
    (clock clockSave padRows wordWidth retireCount control savedControl gap window dst acc trash pubTmp lineRows outAcc pubSaved : Fin tapeCount)
    (hreg : [clock,clockSave,padRows,wordWidth,retireCount,control,savedControl,gap,window,extra 1,dst,acc,trash,pubTmp,lineRows,outAcc,pubSaved].Nodup)
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
    (hsrc : S.R (extra 1) =
      (List.ofFn fun i => (List.ofFn fun j => cstream (prime+K) batch.W (rows.values i j)).flatten).flatten)
    (hcount : S.R (extra 4) = [])
    (hcodec : ∀ i ∈ [planeReg false,planeReg true,extra 2,extra 3,extra 5,extra 6], S.R i = [])
    (hdst : S.R dst = (List.ofFn ambient).flatten++outputTail)
    (hclock : (S.R clock).length = 2^b) (hclockSave : S.R clockSave = [])
    (hpadRows : (S.R padRows).length = (2^a-batch.records.length)*g.length)
    (hwordWidth : (S.R wordWidth).length = batch.W) (hlineRows : (S.R lineRows).length = s)
    (hc : S.R control = gatherControls (prime+K) ((coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).gaps batch.W))
    (hwindow : (S.R window).length = g.length*batch.W)
    (hclean : ∀ i ∈ [retireCount,savedControl,gap,acc,trash,pubTmp,pubSaved], S.R i = [])
    (houtAcc : S.R outAcc = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ ((6*(2^(a+b)*(L*batch.W))+4*(S.R (extra 1)).length+4*(L*batch.W)+9*(a+b)+14)+
        (26*(2^a*(2^b*(L*batch.W)))+24+2*restoringTimeCost hstates a b (L*batch.W) V))+
        (replicaPublicationCost (2^b) s (2^a-batch.records.length) g.length batch.W+6*(2^b)+6) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        ((2*(6*(2^(a+b)*(L*batch.W))+4*(S.R (extra 1)).length+4*(L*batch.W)+9*(a+b)+14)+
          (40*(2^a*(2^b*(L*batch.W)))+38+restoringStockAllowance hstates a b (L*batch.W) V))+
          2*(replicaPublicationCost (2^b) s (2^a-batch.records.length) g.length batch.W+6*(2^b)+6))) depth
        (.seq (.seq (ownedPrefixPadding exponent packet (extra 1) pad tmp saved (pairSym (prime+K) false false))
          (program hstates))
          (restoringReplicaPublication clock clockSave padRows wordWidth retireCount control savedControl gap window (extra 1) dst acc trash pubTmp lineRows outAcc pubSaved))
        (mk v S) n
        (mk v' {S with L := (fun _ => []), R := (Function.update (Function.update S.R (extra 1) []) dst
          ((List.ofFn fun j => g.output batch.W hw (rows.classRows g hkeys j) (ambient j)).flatten++outputTail))}) := by
  obtain ⟨padded,hp,hreal,v₁,n₁,hu₁,hn₁,he₁⟩ := prepare_rows_exec_within body hstates a b L batch.W V
    hpacket hbits hfit hA exponent packet pad tmp saved hpadReg hcapacity rows.values rows.length depth v S
    hexponent hpacketWidth hpad htmp hsaved ha hb hseed hz hwidth hblank hstageCount hL hfresh hsrc hcount hcodec
  let M : Stacks tapeCount (prime+K) := {S with L := (fun _ => []), R := (Function.update S.R (extra 1)
    ((List.ofFn fun j => cstream (prime+K) batch.W (List.ofFn fun i => padded i j).flatten).flatten))}
  have hstable (i : Fin tapeCount) (hi : i ≠ extra 1) : M.R i = S.R i := by simp only [M,Function.update_of_ne hi]
  have hr := hreg
  regs_ne hr
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := rows.scatter_exec_within body g hkeys hcoreWidth hw hlength hw1
    hcapacity padded hp hreal ambient hambient
    clock clockSave padRows wordWidth retireCount control savedControl gap window (extra 1) dst acc trash pubTmp lineRows outAcc pubSaved
    hreg [] outputTail v₁ M
    (by simp only [M,Function.update_self,List.append_nil])
    (by rw [hstable _ ‹extra 1 ≠ dst›.symm]; exact hdst)
    (by rw [hstable _ ‹clock ≠ extra 1›]; exact hclock)
    (by rw [hstable _ ‹clockSave ≠ extra 1›]; exact hclockSave)
    (by rw [hstable _ ‹padRows ≠ extra 1›]; exact hpadRows)
    (by rw [hstable _ ‹wordWidth ≠ extra 1›]; exact hwordWidth)
    (by rw [hstable _ ‹extra 1 ≠ lineRows›.symm]; exact hlineRows)
    (by rw [hstable _ ‹control ≠ extra 1›]; exact hc)
    (by rw [hstable _ ‹window ≠ extra 1›]; exact hwindow)
    (by
      intro i hi
      have hoff : i ≠ extra 1 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | assumption | (apply Ne.symm; assumption)
      rw [hstable _ hoff]
      exact hclean i hi)
    (by rw [hstable _ ‹extra 1 ≠ outAcc›.symm]; exact houtAcc) depth
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,?_⟩
  simpa only [M,Function.update_idem] using mn_seq_within_add he₁ he₂

end
end PackedTranspose
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
