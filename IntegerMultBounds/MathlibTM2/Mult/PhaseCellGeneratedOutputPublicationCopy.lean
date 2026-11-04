module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedOutputPublicationCopy
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! The numerical handoff borrows replica/packet counters to generate its copy
width. The generated counter is retired before returning the ordered stream. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedExactBatch
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A s t B L : ℕ} [NeZero s] [NeZero t] {P U : Type}

def copyWidthSetupCost (B L w : ℕ) := B*(4*(L*w)+9)+4

def generatedOutputCopyTimeCost (N B L w oldVolume : ℕ) :=
  copyWidthSetupCost B L w+(reverseCopyRowsCost N (B*L*w)+2*oldVolume+2)+(2*(B*(L*w))+2)

def generatedOutputCopyStock (N B L w : ℕ) :=
  2*copyWidthSetupCost B L w+2*reverseCopyRowsCost N (B*L*w)


def generatedOutputCopyProgram (replicas packet count savedCount width source archive dst saved tmp : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct replicas packet width saved tmp)
    (.seq (.seq (reverseCopyRows count savedCount width source archive dst saved tmp) (uclear source)) (uclear width))

theorem generated_move_outputs_exec_within
    (body : P → Pr P T Q A U) (batch : PackedExactBatch A s t B L)
    (outputs : List (List (Fin (A+4))))
    (hgood : List.Forall₂ PackedNormalizedJob.output batch.records outputs)
    (replicas packet count savedCount width source archive dst saved tmp : Fin T)
    (hreg : [replicas,packet,count,savedCount,width,source,archive,dst,saved,tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A)
    (hreplicas : (S.R replicas).length = B) (hpacket : (S.R packet).length = L*batch.W)
    (hcount : (S.R count).length = batch.records.length) (hwidth : S.R width = [])
    (hsource : S.R source = outputs.reverse.flatten)
    (hfresh : ∀ k ∈ [savedCount,archive,saved,tmp], S.R k = []) (depth : ℕ) :
    ∃ rows : batch.Rows, ∃ v' n, v'.user = v.user ∧
      n ≤ generatedOutputCopyTimeCost batch.records.length B L batch.W outputs.reverse.flatten.length ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        generatedOutputCopyStock batch.records.length B L batch.W) depth
        (generatedOutputCopyProgram replicas packet count savedCount width source archive dst saved tmp)
        (Host.mk v S) n
        (Host.mk v' {S with R := Function.update (Function.update S.R dst (rows.stream++S.R dst)) source []}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := replicas) (b := packet) (dst := width) (t₁ := saved) (t₂ := tmp) (by regs_nodup) v S
    (hfresh _ (by simp)) (hfresh _ (by simp))
  rw [hreplicas,hpacket] at hn₁ he₁
  simp only [hwidth,List.append_nil] at he₁
  let M : Stacks T A := {S with R := Function.update S.R width (List.replicate (B*(L*batch.W)) tick)}
  have hnative : mnNativePushBound 2 (unaryProduct (P := P) (Q := Q) (A := A) (U := U) replicas packet width saved tmp) := by
    simp [unaryProduct,ucopy,umulSym,scanP,scanR,drainR,popDo,popPush,keepIn,pushN,moveR,moveStep,whileR,peekR,
      mnNativePushBound,mnActPush]
  have hw₁ := mn_native_exec_within he₁ 2 hnative depth
    (mnSize (Host.mk v S)+depth+2*copyWidthSetupCost B L batch.W) (by unfold copyWidthSetupCost; omega)
  have hstable (i : Fin T) (hi : i ≠ width) : M.R i = S.R i := by simp [M,hi]
  obtain ⟨rows,v₂,n₂,hu₂,hn₂,he₂⟩ := move_outputs_for_publication_exec_within body batch outputs hgood
    count savedCount width source archive dst saved tmp (by regs_nodup) v₁ M
    (by rw [hstable _ ‹count ≠ width›]; exact hcount)
    (by simp [M,Nat.mul_assoc])
    (by rw [hstable _ ‹width ≠ source›.symm]; exact hsource)
    (by
      intro i hi
      have ho : i ≠ width := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl
        all_goals first | assumption | (apply Ne.symm; assumption)
      rw [hstable _ ho]
      exact hfresh i hi) depth
  let F : Stacks T A := {M with R := Function.update (Function.update M.R dst (rows.stream++M.R dst)) source []}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) width v₂ F
  have hwlen : (F.R width).length = B*(L*batch.W) := by simp [F,M,‹width ≠ source›,‹width ≠ dst›]
  rw [hwlen] at he₃
  have hw₃ := mn_native_exec_within he₃ 0 (by simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]) depth
    (mnSize (Host.mk v₂ F)+depth+0) (by omega)
  have hend : {F with R := Function.update F.R width []} =
      {S with R := Function.update (Function.update S.R dst (rows.stream++S.R dst)) source []} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi : i = width
    · subst i; simp [‹width ≠ source›,‹width ≠ dst›,hwidth]
    by_cases hs : i = source
    · subst i; simp [F,hi]
    by_cases hd : i = dst
    · subst i; simp [F,M,hi,hs]
    · simp [F,M,hi,hs,hd]
  rw [hend] at hw₃
  have hwhole := mn_seq_within_add hw₁ (mn_seq_within_add he₂ hw₃)
  refine ⟨rows,v₃,n₁+(n₂+(2*(B*(L*batch.W))+2)),hu₃.trans (hu₂.trans hu₁),?_,?_⟩
  · unfold generatedOutputCopyTimeCost copyWidthSetupCost
    change n₁ ≤ copyWidthSetupCost B L batch.W at hn₁
    unfold copyWidthSetupCost at hn₁
    omega
  · simpa only [generatedOutputCopyStock,generatedOutputCopyProgram,Nat.add_zero,Nat.add_assoc] using hwhole

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedExactBatch
