module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedOutputPublicationRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReversePackedLines
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.StackLifecycleResources

/-! Generate the job width from retained dimensions and consume the actual
reverse-job result into forward publication order. Both generated controls are
retired. No output count or computed row stream is supplied by the caller. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedExactBatch
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A s t B L : ℕ} [NeZero s] [NeZero t] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def generatedExport (numerical : Fin T)
    (rowCount replicas packet clock volume dst saved tmp : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct replicas packet volume saved tmp)
    (.seq (retainedReversePackedLines rowCount clock volume numerical dst saved tmp)
      (uclear volume))

def generatedExportCost (N B packet : ℕ) : ℕ :=
  (B*(4*packet+9)+4)+(N*(6*(B*packet)+13)+6)+(2*(B*packet)+2)

/-- Header generation and erasure are linear in the exported payload for a
nonempty class. Empty classes are handled separately by the outer branch. -/
theorem generatedExportCost_le (N B packet : ℕ) (hN : 1 ≤ N) (hpacket : 1 ≤ packet) :
    generatedExportCost N B packet ≤ 21*(N*(B*packet))+13*N+12 := by
  have hB : B ≤ B*packet := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left B hpacket
  have hvolume : B*packet ≤ N*(B*packet) := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (B*packet) hN
  dsimp only [generatedExportCost]
  nlinarith only [hB,hvolume]

/-- Actual certified output determines the exported bytes. The three retained
masters survive; generated controls and scratch return empty. Reversal changes
job order only, preserving each job's replicas and the two borrowed suffixes. -/
theorem generatedExport_exec
    (numerical : Fin T)
    (rowCount replicas packet clock volume dst saved tmp : Fin T)
    (hreg : [rowCount,replicas,packet,clock,volume,numerical,dst,saved,tmp].Nodup)
    (batch : PackedExactBatch A s t B L) (outputs : List (List (Fin (A+4))))
    (houtputs : List.Forall₂ PackedNormalizedJob.output batch.records outputs)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hrows : (S.R rowCount).length = batch.records.length)
    (hreplicas : (S.R replicas).length = B) (hpacket : (S.R packet).length = L*batch.W)
    (hresult : S.R numerical = outputs.reverse.flatten++tail)
    (hfresh : ∀ i ∈ [clock,volume,saved,tmp], S.R i = []) :
    ∃ rows : batch.Rows, ∃ v' n, v'.user = v.user ∧
      n ≤ generatedExportCost batch.records.length B (L*batch.W) ∧
      let F := {S with R := (Function.update (Function.update S.R numerical tail)
        dst (rows.stream++S.R dst))}
      mnSize (Host.mk v' F) = mnSize (Host.mk v S) ∧
      Exec body (generatedExport numerical rowCount replicas packet clock volume dst saved tmp)
        (Host.mk v S) n (Host.mk v' F) ∧
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        2*generatedExportCost batch.records.length B (L*batch.W)) depth
        (generatedExport numerical rowCount replicas packet clock volume dst saved tmp)
        (Host.mk v S) n (Host.mk v' F) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨rows,hwords⟩ := rows_of_outputs batch outputs houtputs
  have hstream : outputs.flatten = rows.stream := by rw [hwords]; rfl
  have hlen : ∀ word ∈ outputs, word.length = B*(L*batch.W) := by
    rw [hwords]
    intro word hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    rw [length_flatten_const _ (by
      intro word hw
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
      rw [length_cstream,rows.length]),List.length_ofFn]
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := replicas) (b := packet) (dst := volume) (t₁ := saved) (t₂ := tmp)
    (by regs_nodup) v S (hfresh _ (by simp)) (hfresh _ (by simp))
  let M : Stacks T A := {S with R := Function.update S.R volume (List.replicate (B*(L*batch.W)) tick)}
  have he₁' : Exec body (unaryProduct replicas packet volume saved tmp) (Host.mk v S) n₁ (Host.mk v₁ M) := by
    simpa only [hreplicas,hpacket,hfresh volume (by simp),List.append_nil] using he₁
  rw [hreplicas,hpacket] at hn₁
  have hkeep (i : Fin T) (hi : i ≠ volume) : M.R i = S.R i := by
    simp only [M,Function.update_of_ne hi]
  obtain ⟨v₂,E,n₂,hu₂,hn₂,he₂,hs,hd,hi,ho,hl,hframe⟩ := retainedReversePackedLines_exec (body := body)
    rowCount clock volume numerical dst saved tmp (by regs_nodup)
    outputs.reverse (B*(L*batch.W)) (by intro word hw; exact hlen word (List.mem_reverse.mp hw))
    tail v₁ M
    (by rw [hkeep _ ‹rowCount ≠ volume›,List.length_reverse,←houtputs.length_eq]; exact hrows)
    (by simp [M])
    (by rw [hkeep _ ‹volume ≠ numerical›.symm]; exact hresult)
    (by rw [hkeep _ ‹clock ≠ volume›]; exact hfresh _ (by simp))
    (by rw [hkeep _ ‹volume ≠ saved›.symm]; exact hfresh _ (by simp))
    (by rw [hkeep _ ‹volume ≠ tmp›.symm]; exact hfresh _ (by simp))
  simp only [List.length_reverse,←houtputs.length_eq] at hn₂
  have hE : E = {M with R := (Function.update (Function.update M.R numerical tail)
      dst (rows.stream++M.R dst))} := by
    refine Stacks.ext hi ho hl ?_
    funext i
    by_cases his : i = numerical
    · subst i; simpa only [Function.update_of_ne ‹numerical ≠ dst›,Function.update_self] using hs
    by_cases hid : i = dst
    · subst i; simpa only [Function.update_self,List.reverse_reverse,hstream] using hd
    · simpa only [Function.update_of_ne his,Function.update_of_ne hid] using hframe i his hid
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) volume v₂ E
  have hvolume : (E.R volume).length = B*(L*batch.W) := by
    rw [hframe volume ‹volume ≠ numerical› ‹volume ≠ dst›]
    simp [M]
  rw [hvolume] at he₃
  let F : Stacks T A := {S with R := (Function.update (Function.update S.R numerical tail)
    dst (rows.stream++S.R dst))}
  have hend : {E with R := Function.update E.R volume []} = F := by
    rw [hE]
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hv : i = volume
    · subst i; simp [F,‹volume ≠ dst›,‹volume ≠ numerical›,hfresh]
    · simp [M,F,hv,‹volume ≠ dst›.symm,Function.update_apply]
  rw [hend] at he₃
  have hex := Exec.seq he₁' (Exec.seq he₂ he₃)
  have hn : n₁+(n₂+(2*(B*(L*batch.W))+2)) ≤
      generatedExportCost batch.records.length B (L*batch.W) := by
    dsimp only [generatedExportCost]
    omega
  have hnative : mnNativePushBound 2
      (generatedExport (P := P) (Q := Q) (A := A) (U := U)
        numerical rowCount replicas packet clock volume dst saved tmp) := by
    simp only [generatedExport,mnNativePushBound]
    refine ⟨?_,retainedReversePackedLines_pushBound _ _ _ _ _ _ _,?_⟩
    · simp [unaryProduct,ucopy,umulSym,scanP,scanR,keepIn,drainR,popDo,popPush,
        pushN,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
    · simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]
  have hsize : mnSize (Host.mk v₃ F) = mnSize (Host.mk v S) := by
    have hload : mnSize (Host.mk v₁ M) = mnSize (Host.mk v S)+B*(L*batch.W) := by
      have hh := mn_size_update (Host.mk v S) v₁ (.rt volume) (List.replicate (B*(L*batch.W)) tick)
      have hbalance : mnSize (Host.mk v₁ M)+(S.R volume).length =
          mnSize (Host.mk v S)+(List.replicate (B*(L*batch.W)) (tick : Fin (A+4))).length := by
        simpa only [M,Host.mk,update_rt,get_rt] using hh
      rw [hfresh _ (by simp),List.length_nil,List.length_replicate] at hbalance
      omega
    have hmove : mnSize (Host.mk v₂ E) = mnSize (Host.mk v₁ M) := by
      let R : Stacks T A := {M with R := Function.update M.R numerical tail}
      have ha : mnSize (Host.mk v₂ R)+(M.R numerical).length =
          mnSize (Host.mk v₁ M)+tail.length := by
        simpa only [R,Host.mk,update_rt,get_rt] using
          mn_size_update (Host.mk v₁ M) v₂ (.rt numerical) tail
      have hb : mnSize (Host.mk v₂ E)+(M.R dst).length =
          mnSize (Host.mk v₂ R)+(rows.stream++M.R dst).length := by
        simpa only [hE,R,Host.mk,update_rt,get_rt,
          Function.update_of_ne ‹numerical ≠ dst›.symm] using
          mn_size_update (Host.mk v₂ R) v₂ (.rt dst) (rows.stream++M.R dst)
      have hslen : (M.R numerical).length = rows.stream.length+tail.length := by
        rw [hkeep _ ‹volume ≠ numerical›.symm,hresult,List.length_append]
        have hh := congrArg List.length hstream
        simpa only [List.length_flatten,List.map_reverse,List.sum_reverse] using
          congrArg (fun n => n+tail.length) hh
      simp only [List.length_append] at hb
      omega
    have hclear := mn_size_update (Host.mk v₂ E) v₃ (.rt volume) []
    have hh : mnSize (Host.mk v₃ {E with R := Function.update E.R volume []})+(E.R volume).length =
        mnSize (Host.mk v₂ E)+([] : List (Fin (A+4))).length := by
      simpa only [Host.mk,update_rt,get_rt] using hclear
    rw [hend,hvolume,List.length_nil] at hh
    omega
  exact ⟨rows,v₃,_,hu₃.trans (hu₂.trans hu₁),hn,hsize,hex,
    fun depth => mn_native_exec_within hex 2 hnative depth _ (by omega)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedExactBatch
