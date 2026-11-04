module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedClassPublicationReplica
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedClassScatter
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedPublicationPages
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterchangeHeaderStock
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Generate the shared scatter pages from retained origins, publish actual
computed class rows, then retire the pages. Every borrowed register is restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedExactBatch
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A s t B L width C : ℕ} [NeZero s] [NeZero t] {P U : Type}
  {batch : PackedExactBatch A s t B L}

theorem Rows.generated_scatter_exec_within (body : P → Pr P T Q A U) (rows : batch.Rows)
    (g : CorePublicationClass s width) (hkeys : batch.records.map (fun r => r.k) = g.indices)
    (hwidth : ∀ r ∈ batch.records, r.coreWidth = width) (hw : 0 < width)
    (hlength : L = g.length) (hw1 : 1 ≤ batch.W) (hcapacity : batch.records.length ≤ C)
    (padded : Fin C → Fin B → List GaussianInt) (hlen : ∀ i j, (padded i j).length = L)
    (hreal : ∀ i j, padded (paddedCoreIndex hcapacity i) j = rows.values i j)
    (ambient : Fin B → List (Fin (A+4))) (hambient : ∀ j, (ambient j).length = s*batch.W)
    (e : Fin 117 → Fin T) (he : Function.Injective e) (V : ℕ)
    (clock clockSave padRows wordWidth retireCount savedControl gap src dst acc trash tmp lineRows outAcc saved : Fin T)
    (hreg : [clock,clockSave,padRows,wordWidth,retireCount,(e 92),savedControl,gap,(e 103),src,dst,acc,trash,tmp,lineRows,outAcc,saved].Nodup)
    (sourceTail outputTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = (List.ofFn fun j => cstream A batch.W (List.ofFn fun i => padded i j).flatten).flatten++sourceTail)
    (hdst : S.R dst = (List.ofFn ambient).flatten++outputTail)
    (hclock : (S.R clock).length = B) (hclockSave : S.R clockSave = [])
    (hpadRows : (S.R padRows).length = (C-batch.records.length)*g.length)
    (hwordWidth : (S.R wordWidth).length = batch.W) (hlineRows : (S.R lineRows).length = s)
    (hwV : batch.W < 2^V) (hsV : s < 2^V) (hvolume : s*batch.W < 2^V)
    (originTail : List (Fin (A+4)))
    (hV : (S.R (e 115)).length = V) (hpageWidth : (S.R (e 94)).length = batch.W)
    (hpageLength : (S.R (e 102)).length = g.length)
    (hOrigins : S.R (e 109) =
      (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).origins.flatMap (binSyms V)++originTail)
    (hpageCount : S.R (e 116) = List.replicate
      (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).origins.length tick)
    (hblank : ∀ k : Fin 117, k.val < 19 → S.R (e k) = [])
    (hfresh : ∀ k ∈ [(88 : Fin 117),89,90,91,92,103,104,105,106,107], S.R (e k) = [])
    (hclean : ∀ i ∈ [retireCount,savedControl,gap,acc,trash,tmp,saved], S.R i = [])
    (houtAcc : S.R outAcc = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (prepareReplicaPublicationPagesCost V s g.length batch.W g.indices.length+
        (replicaPublicationCost B s (C-batch.records.length) g.length batch.W+6*B+6))+
        (2*(g.length*batch.W+(gatherControls A ((coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).gaps batch.W)).length)+5) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        (mnProgPush (prepareReplicaPublicationPages (P := Empty) (Q := Q) (A := A) (U := U))*
          prepareReplicaPublicationPagesCost V s g.length batch.W g.indices.length+2*(replicaPublicationCost B s (C-batch.records.length) g.length batch.W+6*B+6))) depth
        (.seq (embProg e Empty.elim (prepareReplicaPublicationPages (P := Empty)))
          (.seq (restoringReplicaPublication clock clockSave padRows wordWidth retireCount (e 92) savedControl gap (e 103) src dst acc trash tmp lineRows outAcc saved)
            (clearWords [e 103,e 92])))
        (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R src sourceTail) dst
          ((List.ofFn fun j => g.output batch.W hw (rows.classRows g hkeys j) (ambient j)).flatten++outputTail))}) := by
  let windows := coreSubsetPublicationWindows s width g.length hw g.indices g.sublist
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := placedPublicationPages_exec_within body e he V batch.W windows hw1 hwV hsV hvolume
    v S originTail hV hpageWidth hpageLength hOrigins hpageCount hblank hfresh depth
  have hcount : windows.origins.length = g.indices.length := by
    simp [windows,coreSubsetPublicationWindows,PublicationWindows.restrict]
  rw [hcount] at hn₁ he₁
  let M : Stacks T A := {S with R := (Function.update (Function.update S.R (e 103)
    (List.replicate (g.length*batch.W) tick)) (e 92) (gatherControls A (windows.gaps batch.W)))}
  have hstable (i : Fin T) (hi : i ≠ e 103) (hj : i ≠ e 92) : M.R i = S.R i := by simp [M,hi,hj]
  have hr := hreg
  regs_ne hr
  have hpageNe : e 103 ≠ e 92 := he.ne (by decide)
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := rows.scatter_exec_within body g hkeys hwidth hw hlength hw1 hcapacity
    padded hlen hreal ambient hambient
    clock clockSave padRows wordWidth retireCount (e 92) savedControl gap (e 103) src dst acc trash tmp lineRows outAcc saved
    hreg sourceTail outputTail v₁ M
    (by rw [hstable _ ‹e 103 ≠ src›.symm ‹e 92 ≠ src›.symm]; exact hsrc)
    (by rw [hstable _ ‹e 103 ≠ dst›.symm ‹e 92 ≠ dst›.symm]; exact hdst)
    (by rw [hstable _ ‹clock ≠ e 103› ‹clock ≠ e 92›]; exact hclock)
    (by rw [hstable _ ‹clockSave ≠ e 103› ‹clockSave ≠ e 92›]; exact hclockSave)
    (by rw [hstable _ ‹padRows ≠ e 103› ‹padRows ≠ e 92›]; exact hpadRows)
    (by rw [hstable _ ‹wordWidth ≠ e 103› ‹wordWidth ≠ e 92›]; exact hwordWidth)
    (by rw [hstable _ ‹e 103 ≠ lineRows›.symm ‹e 92 ≠ lineRows›.symm]; exact hlineRows)
    (by simp only [M,windows,Function.update_self])
    (by simp [M,hpageNe])
    (by
      intro i hi
      have hoff : i ≠ e 103 ∧ i ≠ e 92 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals constructor <;> first | assumption | (apply Ne.symm; assumption)
      rw [hstable _ hoff.1 hoff.2]
      exact hclean i hi)
    (by rw [hstable _ ‹e 103 ≠ outAcc›.symm ‹e 92 ≠ outAcc›.symm]; exact houtAcc) depth
  let F : Stacks T A := {M with R := (Function.update (Function.update M.R src sourceTail) dst
    ((List.ofFn fun j => g.output batch.W hw (rows.classRows g hkeys j) (ambient j)).flatten++outputTail))}
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) [e 103,e 92] (by simp [hpageNe]) v₂ F
  have hvol : ([e 103,e 92].map (fun i => (F.R i).length)).sum =
      g.length*batch.W+(gatherControls A (windows.gaps batch.W)).length := by
    simp [F,M,‹e 103 ≠ src›,‹e 103 ≠ dst›,‹e 92 ≠ src›,‹e 92 ≠ dst›,hpageNe]
  rw [hvol] at he₃
  simp only [List.length_cons,List.length_nil] at he₃
  have ht := mn_native_exec_within he₃ 0 (clearWords_native _) depth (mnSize (Host.mk v₂ F)+depth+0) (by omega)
  have hfinal : {F with R := fun i => if i ∈ [e 103,e 92] then [] else F.R i} =
      {S with R := (Function.update (Function.update S.R src sourceTail) dst
        ((List.ofFn fun j => g.output batch.W hw (rows.classRows g hkeys j) (ambient j)).flatten++outputTail))} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi : i = e 103
    · subst i
      simp [hfresh 103 (by simp),‹e 103 ≠ src›,‹e 103 ≠ dst›]
    by_cases hj : i = e 92
    · subst i
      simp [hfresh 92 (by simp),‹e 92 ≠ src›,‹e 92 ≠ dst›]
    · simp [F,M,Function.update_apply,hi,hj]
  rw [hfinal] at ht
  have hwhole := mn_seq_within_add he₁ (mn_seq_within_add he₂ ht)
  refine ⟨v₃,n₁+(n₂+(2*(g.length*batch.W+(gatherControls A (windows.gaps batch.W)).length)+5)),
    hu₃.trans (hu₂.trans hu₁),?_,?_⟩
  · simpa only [windows,Nat.add_assoc] using
      Nat.add_le_add_right (Nat.add_le_add hn₁ hn₂)
        (2*(g.length*batch.W+(gatherControls A (windows.gaps batch.W)).length)+5)
  · simpa only [Nat.add_zero,windows] using hwhole

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedExactBatch
