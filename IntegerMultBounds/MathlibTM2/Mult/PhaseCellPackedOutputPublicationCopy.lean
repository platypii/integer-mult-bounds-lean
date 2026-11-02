module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedOutputPublicationRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReverseCopyRows

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

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedExactBatch
