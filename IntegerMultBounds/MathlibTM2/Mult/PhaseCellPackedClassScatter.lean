module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedClassPublicationReplica
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoringReplicaPublication

/-! Execute class scatter on actual transposed computed rows. The transpose's
real-row identity supplies all numerical row and padding premises. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedExactBatch
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A s t B L width C : ℕ} [NeZero s] [NeZero t] {P U : Type}
  {batch : PackedExactBatch A s t B L}

theorem Rows.scatter_exec_within (body : P → Pr P T Q A U) (rows : batch.Rows)
    (g : CorePublicationClass s width) (hkeys : batch.records.map (fun r => r.k) = g.indices)
    (hwidth : ∀ r ∈ batch.records, r.coreWidth = width) (hw : 0 < width)
    (hlength : L = g.length) (hw1 : 1 ≤ batch.W) (hcapacity : batch.records.length ≤ C)
    (padded : Fin C → Fin B → List GaussianInt) (hlen : ∀ i j, (padded i j).length = L)
    (hreal : ∀ i j, padded (paddedCoreIndex hcapacity i) j = rows.values i j)
    (ambient : Fin B → List (Fin (A+4))) (hambient : ∀ j, (ambient j).length = s*batch.W)
    (clock clockSave padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved : Fin T)
    (hreg : [clock,clockSave,padRows,wordWidth,retireCount,control,savedControl,gap,window,src,dst,acc,trash,tmp,lineRows,outAcc,saved].Nodup)
    (sourceTail outputTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = (List.ofFn fun j => cstream A batch.W (List.ofFn fun i => padded i j).flatten).flatten++sourceTail)
    (hdst : S.R dst = (List.ofFn ambient).flatten++outputTail)
    (hclock : (S.R clock).length = B) (hclockSave : S.R clockSave = [])
    (hpadRows : (S.R padRows).length = (C-batch.records.length)*g.length)
    (hwordWidth : (S.R wordWidth).length = batch.W) (hlineRows : (S.R lineRows).length = s)
    (hc : S.R control = gatherControls A ((coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).gaps batch.W))
    (hwindow : (S.R window).length = g.length*batch.W)
    (hclean : ∀ i ∈ [retireCount,savedControl,gap,acc,trash,tmp,saved], S.R i = [])
    (houtAcc : S.R outAcc = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ replicaPublicationCost B s (C-batch.records.length) g.length batch.W+6*B+6 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        2*(replicaPublicationCost B s (C-batch.records.length) g.length batch.W+6*B+6)) depth
        (restoringReplicaPublication clock clockSave padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved)
        (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R src sourceTail) dst
          ((List.ofFn fun j => g.output batch.W hw (rows.classRows g hkeys j) (ambient j)).flatten++outputTail))}) := by
  let replicas := List.ofFn (rows.publicationReplica g hkeys padded ambient)
  let windows := coreSubsetPublicationWindows s width g.length hw g.indices g.sublist
  have hvalid : ∀ r ∈ replicas, r.Valid windows batch.W (C-batch.records.length) := by
    intro r hr
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    exact rows.publicationReplica_valid g hkeys hwidth hw hlength hcapacity padded hlen hreal ambient hambient j
  obtain ⟨v',F,n,hu,hn,he,hs,hd,hi,ho,hl,hframe⟩ := restoringReplicaPublication_exec
    clock clockSave padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved
    hreg windows batch.W (C-batch.records.length) hw1 replicas hvalid sourceTail outputTail v S
    (by simpa [replicas,List.flatMap_def,List.map_ofFn,Function.comp_def,Rows.publicationReplica,PublicationReplica.input] using hsrc)
    (by simpa [replicas,List.flatMap_def,List.map_ofFn,Function.comp_def,Rows.publicationReplica] using hdst)
    (by simpa [replicas] using hclock) hclockSave hpadRows hwordWidth hlineRows hc hwindow hclean houtAcc
  simp only [replicas,List.length_ofFn] at hn
  have hr := hreg
  regs_ne hr
  have hend : F = {S with R := (Function.update (Function.update S.R src sourceTail) dst
      ((List.ofFn fun j => g.output batch.W hw (rows.classRows g hkeys j) (ambient j)).flatten++outputTail))} := by
    refine Stacks.ext hi ho hl ?_
    funext i
    by_cases his : i = src
    · subst i
      simpa only [Function.update_of_ne ‹src ≠ dst›,Function.update_self] using hs
    by_cases hid : i = dst
    · subst i
      simpa only [replicas,List.flatMap_def,List.map_ofFn,Function.comp_def,windows,
        Rows.publicationReplica_output,Function.update_self] using hd
    · simpa only [Function.update_of_ne his,Function.update_of_ne hid] using hframe i his hid
  refine ⟨v',n,hu,hn,?_⟩
  exact (restoringReplicaPublication_within he hn depth).cast rfl (congrArg (Host.mk v') hend)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedExactBatch
