module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpBatch
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBatchSetup

/-! # Shared batch extraction from unary dimensions

Generate skip/record counters once, extract every record of the shared product stream,
then clear the three generated words. Only the destination changes.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Setup and cleanup are outside the record loop. -/
def correlationBatchFromUnary
    (lR triples dst batch batchSaved skip savedSkip mR recordSaved wR recordSymbols src
      acc current savedSource saved buf tmp : Fin T) : Pr P T Q A U :=
  .seq (correlationBatchSetup lR wR mR triples skip recordSymbols current buf tmp)
    (.seq (correlationBatch batch batchSaved skip savedSkip mR recordSaved wR recordSymbols
      src acc current savedSource saved buf tmp dst) (clearWords [triples, skip, recordSymbols]))

def correlationBatchUnaryCost (l w m M : ℕ) : ℕ :=
  M * (38 * m * w + 19 * m + 6 * (2 ^ l) * w + 23) +
    18 * m * w + 37 * m + 4 * w + 6 * (2 ^ l * w) + 9 * l + 35

/-- Full shared extraction contract, including all parameter generation and final cleanup. -/
theorem correlationBatchFromUnary_exec
    {lR triples dst batch batchSaved skip savedSkip mR recordSaved wR recordSymbols src
      acc current savedSource saved buf tmp : Fin T}
    (hreg : [lR, triples, dst, batch, batchSaved, skip, savedSkip, mR, recordSaved, wR,
      recordSymbols, src, acc, current, savedSource, saved, buf, tmp].Nodup)
    (l w m M : ℕ) (hsize : 4 * m ≤ 2 ^ l) (X : ℕ → Fin (2 ^ l) → GaussianInt)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A + 4)))
    (hl : (S.R lR).length = l) (hw : (S.R wR).length = w) (hm : (S.R mR).length = m)
    (hbatch : (S.R batch).length = M) (hsrc : S.R src = cstream A w (rpStream M X) ++ tail)
    (howned : ∀ k ∈ [triples, skip, recordSymbols], S.R k = [])
    (hclean : ∀ k ∈ [batchSaved, acc, savedSource, savedSkip, recordSaved, current, saved, buf, tmp], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ correlationBatchUnaryCost l w m M ∧
      Exec body (correlationBatchFromUnary lR triples dst batch batchSaved skip savedSkip mR
        recordSaved wR recordSymbols src acc current savedSource saved buf tmp) (mk v S) n
        (mk v' { S with R := (Function.update S.R dst
          (cstream A w (correlationStream M m X) ++ S.R dst)) }) := by
  have hbatchRegs := (List.nodup_cons.mp (List.nodup_cons.mp hreg).2).2
  have hreg' := hreg
  regs_ne hreg'
  have htriples := howned triples (by simp)
  have hskip := howned skip (by simp)
  have hrecord := howned recordSymbols (by simp)
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := correlationBatchSetup_exec (body := body)
    (show [lR, wR, mR, triples, skip, recordSymbols, current, buf, tmp].Nodup by simp_all [ne_comm])
    l w m v S hl hw hm htriples hskip hrecord
    (hclean _ (by simp)) (hclean _ (by simp)) (hclean _ (by simp))
  set S₁ : Stacks T A := { S with R := (Function.update (Function.update
    (Function.update S.R triples (List.replicate (3 * m) tick)) skip
      (List.replicate (3 * m * w) tick)) recordSymbols (List.replicate (2 ^ l * w) tick)) }
  have off (k : Fin T) (ht : k ≠ triples) (hs : k ≠ skip) (hr : k ≠ recordSymbols) :
      S₁.R k = S.R k := by simp [S₁, ht, hs, hr]
  have clean₁ : ∀ k ∈ [batchSaved, acc, savedSource, savedSkip, recordSaved, current, saved, buf, tmp],
      S₁.R k = [] := by
    intro k hk
    have hc := hclean k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [off _ (by first | assumption | (apply Ne.symm; assumption))
        (by first | assumption | (apply Ne.symm; assumption))
        (by first | assumption | (apply Ne.symm; assumption))] <;> exact hc
  obtain ⟨v₂, hu₂, he₂⟩ := correlationBatch_rpStream_exec (body := body) hbatchRegs w m (2 ^ l) M
    hsize X v₁ S₁ tail
    (by rw [off _ ‹triples ≠ batch›.symm ‹batch ≠ skip› ‹batch ≠ recordSymbols›]; exact hbatch)
    (by rw [off _ ‹triples ≠ src›.symm ‹skip ≠ src›.symm ‹recordSymbols ≠ src›.symm]; exact hsrc)
    (by simp [S₁, ‹skip ≠ recordSymbols›])
    (by rw [off _ ‹triples ≠ mR›.symm ‹skip ≠ mR›.symm ‹mR ≠ recordSymbols›]; exact hm)
    (by rw [off _ ‹triples ≠ wR›.symm ‹skip ≠ wR›.symm ‹wR ≠ recordSymbols›]; exact hw)
    (by simp [S₁]) clean₁
  set S₂ : Stacks T A := { S₁ with R := (Function.update S₁.R dst
    (cstream A w (correlationStream M m X) ++ S₁.R dst)) }
  obtain ⟨v₃, hu₃, he₃⟩ := clearWords_exec (body := body) [triples, skip, recordSymbols]
    (by simp_all) v₂ S₂
  have hsum : ([triples, skip, recordSymbols].map (fun k => (S₂.R k).length)).sum =
      3 * m + 3 * m * w + 2 ^ l * w := by
    simp (disch := first | assumption | (apply Ne.symm; assumption)) [S₂, S₁]
    ring
  refine ⟨v₃, _, hu₃.trans (hu₂.trans hu₁), ?_, (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · rw [hsum]
    simp only [List.length_cons, List.length_nil]
    unfold correlationBatchUnaryCost
    nlinarith [hn₁]
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    clear he₁ he₂ he₃ hu₁ hu₂ hu₃ clean₁ off hclean howned
    funext k
    change (if k ∈ [triples, skip, recordSymbols] then [] else S₂.R k) = _
    by_cases ht : k = triples
    · subst k
      simp (disch := first | assumption | (apply Ne.symm; assumption)) [htriples]
    by_cases hs : k = skip
    · subst k
      simp (disch := first | assumption | (apply Ne.symm; assumption)) [hskip]
    by_cases hr : k = recordSymbols
    · subst k
      simp (disch := first | assumption | (apply Ne.symm; assumption)) [hrecord]
    · simp only [List.mem_cons, List.not_mem_nil, ht, hs, hr, or_self, ite_false]
      by_cases hd : k = dst
      · subst k
        simp (disch := first | assumption | (apply Ne.symm; assumption)) [S₂, S₁]
      · simp [S₂, S₁, hd, ht, hs, hr]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
