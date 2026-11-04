module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedOutputPublicationRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReverseCopyRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterchangeHeaderStock

/-! Convert the actual reverse-job result tape into an ordered publication
stream using the existing restoring row scan. No output-row data are assumed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedExactBatch
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A s t B L : ℕ} [NeZero s] [NeZero t] {P U : Type}

theorem copy_outputs_for_publication_exec_within
    (body : P → Pr P T Q A U) (batch : PackedExactBatch A s t B L)
    (outputs : List (List (Fin (A+4))))
    (hgood : List.Forall₂ PackedNormalizedJob.output batch.records outputs)
    (count savedCount width source archive dst saved tmp : Fin T)
    (hreg : [count,savedCount,width,source,archive,dst,saved,tmp].Nodup)
    (borrowed : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hcount : (S.R count).length = batch.records.length)
    (hwidth : (S.R width).length = B*L*batch.W)
    (hsource : S.R source = outputs.reverse.flatten++borrowed)
    (hfresh : ∀ k ∈ [savedCount,archive,saved,tmp], S.R k = []) (depth : ℕ) :
    ∃ rows : batch.Rows, ∃ v' n, v'.user = v.user ∧
      n ≤ reverseCopyRowsCost batch.records.length (B*L*batch.W) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        2*reverseCopyRowsCost batch.records.length (B*L*batch.W)) depth
        (reverseCopyRows count savedCount width source archive dst saved tmp) (Host.mk v S) n
        (Host.mk v' {S with R := Function.update S.R dst (rows.stream++S.R dst)}) := by
  obtain ⟨rows,hwords⟩ := rows_of_outputs batch outputs hgood
  have hlen : ∀ word ∈ outputs, word.length = B*L*batch.W := by
    intro word hw
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hw
    have hir : i < batch.records.length := by rw [hgood.length_eq]; exact hi
    have hh : (batch.records[i]'hir).output (outputs[i]'hi) := by
      simpa only [List.get_eq_getElem] using hgood.get hir hi
    rw [PackedNormalizedJob.output_length _ hh,PackedNormalizedJob.outputVolume,
      batch.hreplicas _ (List.getElem_mem hir),batch.hcore _ (List.getElem_mem hir),
      batch.hwidth _ (List.getElem_mem hir)]
  obtain ⟨v',n,hu,hn,he⟩ := reverseCopyRows_exec_within (body := body)
    count savedCount width source archive dst saved tmp hreg (B*L*batch.W) outputs.reverse
    (by intro word hw; exact hlen word (List.mem_reverse.mp hw)) borrowed v S
    (by simpa only [List.length_reverse,←hgood.length_eq] using hcount) hwidth hsource hfresh depth
  simp only [List.length_reverse,←hgood.length_eq,List.reverse_reverse] at hn he
  have hstream : outputs.flatten = rows.stream := by rw [hwords]; rfl
  rw [hstream] at he
  exact ⟨rows,v',n,hu,hn,he⟩


/-- The selected class has no borrowed result suffix. Retire that temporary
result after the restoring copy, retaining the ordered publication stream. -/
theorem move_outputs_for_publication_exec_within
    (body : P → Pr P T Q A U) (batch : PackedExactBatch A s t B L)
    (outputs : List (List (Fin (A+4))))
    (hgood : List.Forall₂ PackedNormalizedJob.output batch.records outputs)
    (count savedCount width source archive dst saved tmp : Fin T)
    (hreg : [count,savedCount,width,source,archive,dst,saved,tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A)
    (hcount : (S.R count).length = batch.records.length)
    (hwidth : (S.R width).length = B*L*batch.W)
    (hsource : S.R source = outputs.reverse.flatten)
    (hfresh : ∀ k ∈ [savedCount,archive,saved,tmp], S.R k = []) (depth : ℕ) :
    ∃ rows : batch.Rows, ∃ v' n, v'.user = v.user ∧
      n ≤ reverseCopyRowsCost batch.records.length (B*L*batch.W)+2*outputs.reverse.flatten.length+2 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        2*reverseCopyRowsCost batch.records.length (B*L*batch.W)) depth
        (.seq (reverseCopyRows count savedCount width source archive dst saved tmp) (uclear source))
        (Host.mk v S) n
        (Host.mk v' {S with R := Function.update (Function.update S.R dst (rows.stream++S.R dst)) source []}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨rows,v₁,n,hu₁,hn,he₁⟩ := copy_outputs_for_publication_exec_within body batch outputs hgood
    count savedCount width source archive dst saved tmp hreg [] v S hcount hwidth
    (by simpa using hsource) hfresh depth
  let M : Stacks T A := {S with R := Function.update S.R dst (rows.stream++S.R dst)}
  obtain ⟨v₂,hu₂,he₂⟩ := uclear_exec (body := body) source v₁ M
  have hlen : (M.R source).length = outputs.reverse.flatten.length := by
    simp only [M,Function.update_of_ne ‹source ≠ dst›,hsource]
  have hwithin := mn_native_exec_within he₂ 0 (by
    simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]) depth
    (mnSize (Host.mk v S)+depth+2*reverseCopyRowsCost batch.records.length (B*L*batch.W))
    (by simpa only [Nat.zero_mul,Nat.add_zero] using he₁.final)
  refine ⟨rows,v₂,n+(2*(M.R source).length+2),hu₂.trans hu₁,?_,he₁.seq hwithin⟩
  rw [hlen]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedExactBatch
