module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpReverseRowsLoop

/-! # Restore a batch of reversed coefficient rows

The source, batch counter, reusable row/word counts and private scratch are restored.
Only the destination gains the reversed rows, in their original batch order.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Length of the concatenation of equal-length coefficient blocks. -/
theorem reverseRows_flatten_length (r : ℕ) (blocks : List (List GaussianInt))
    (hlen : ∀ xs ∈ blocks, xs.length = r) : blocks.flatten.length = blocks.length * r := by
  induction blocks with
  | nil => simp
  | cons xs blocks ih =>
    rw [List.flatten_cons, List.length_append, hlen xs (by simp),
      ih (fun ys hy => hlen ys (by simp [hy])), List.length_cons]
    ring

/-- Reverse all coefficient rows with one reusable set of counters. -/
def reverseRows
    (batch batchSaved rowCount recordSaved wordR recordSymbols src acc current savedSource saved buf tmp dst : Fin T) :
    Pr P T Q A U :=
  .seq (.act (peekR batch)) <|
  .seq (.loop (·.flag) (reverseRowLoopBody batch batchSaved rowCount
    recordSaved wordR recordSymbols src acc current savedSource saved buf tmp)) <|
  .seq (moveR acc dst id) <|
  .seq (moveR batchSaved batch id) (moveR savedSource src id)

/-- Only the destination changes; source, batch counter, reusable counts and scratch are restored. -/
theorem reverseRows_exec
    {dst batch batchSaved rowCount recordSaved wordR recordSymbols src acc current savedSource saved buf tmp : Fin T}
    (hreg : [dst, batch, batchSaved, rowCount, recordSaved, wordR, recordSymbols, src,
      acc, current, savedSource, saved, buf, tmp].Nodup)
    (w r : ℕ) (blocks : List (List GaussianInt))
    (hlen : ∀ xs ∈ blocks, xs.length = r)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A + 4)))
    (hbatch : (S.R batch).length = blocks.length)
    (hsrc : S.R src = cstream A w blocks.flatten ++ tail)
    (hrow : (S.R rowCount).length = r)
    (hw : (S.R wordR).length = w) (hrecord : (S.R recordSymbols).length = r * w)
    (hclean : ∀ k ∈ [batchSaved, acc, savedSource, recordSaved, current, saved, buf, tmp], S.R k = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (reverseRows batch batchSaved rowCount recordSaved wordR
        recordSymbols src acc current savedSource saved buf tmp dst) (mk v S)
        (blocks.length * (26 * r * w + 19 * r + 17) + 8)
        (mk v' { S with R := (Function.update S.R dst
          (cstream A w (blocks.flatMap List.reverse) ++ S.R dst)) }) := by
  have hloop := (List.nodup_cons.mp hreg).2
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := reverseRowLoop_exec (body := body) hloop w r blocks hlen
    (S.R batch) hbatch { v with flag := (S.R batch).head?.isSome } S tail rfl hsrc hrow hw hrecord
    (fun k hk => hclean k (List.mem_append_right [batchSaved, acc, savedSource] hk)) rfl
  set S₁ : Stacks T A := { S with R := (Function.update (Function.update
    (Function.update (Function.update (Function.update S.R batch []) batchSaved
      ((S.R batch).reverse ++ S.R batchSaved)) src tail) savedSource
      ((cstream A w blocks.flatten).reverse ++ S.R savedSource)) acc
      ((cstream A w (blocks.flatMap List.reverse)).reverse ++ S.R acc)) }
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body acc dst ‹dst ≠ acc›.symm id v₁ S₁
  set S₂ : Stacks T A := { S₁ with R := movedR S₁.R acc dst id (S₁.R acc) }
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body batchSaved batch ‹batch ≠ batchSaved›.symm id v₂ S₂
  set S₃ : Stacks T A := { S₂ with R := movedR S₂.R batchSaved batch id (S₂.R batchSaved) }
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body savedSource src ‹src ≠ savedSource›.symm id v₃ S₃
  have hc₁ : S.R batchSaved = [] := hclean _ (by simp)
  have hc₂ : S.R acc = [] := hclean _ (by simp)
  have hc₃ : S.R savedSource = [] := hclean _ (by simp)
  have hflat := reverseRows_flatten_length r blocks hlen
  have hcorr : (blocks.flatMap List.reverse).length = blocks.length * r := by
    simpa [Function.comp_def] using reverseRows_flatten_length r (blocks.map List.reverse) (by
      intro xs hx
      obtain ⟨ys, hy, rfl⟩ := List.mem_map.mp hx
      simpa using hlen ys hy)
  have hp := Exec.act (body := body) (peekR batch) (mk v S)
  rw [peekR_run] at hp
  refine ⟨v₄, hu₄.trans (hu₃.trans (hu₂.trans hu₁)),
    (Exec.seq hp (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄)))).cast ?_ ?_⟩
  · simp (disch := first | assumption | (apply Ne.symm; assumption))
      [S₃, S₂, S₁, movedR, hc₁, hc₂, hc₃, hbatch, hflat, hcorr]
    ring
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    clear he₁ he₂ he₃ he₄ hp hu₁ hu₂ hu₃ hu₄ hclean
    funext k
    by_cases hk0 : k = dst
    · subst k
      simp (disch := first | assumption | (apply Ne.symm; assumption)) only
        [S₃, S₂, S₁, movedR, Function.update_self, Function.update_of_ne,
          hc₁, hc₂, hc₃, List.append_nil, List.map_id, List.reverse_reverse]

    by_cases hk1 : k = batch
    · subst k
      simp (disch := first | assumption | (apply Ne.symm; assumption)) only
        [S₃, S₂, S₁, movedR, Function.update_self, Function.update_of_ne,
          hc₁, hc₂, hc₃, List.append_nil, List.map_id, List.reverse_reverse]

    by_cases hk2 : k = batchSaved
    · subst k
      simp (disch := first | assumption | (apply Ne.symm; assumption)) only
        [S₃, S₂, S₁, movedR, Function.update_self, Function.update_of_ne,
          hc₁, hc₂, hc₃, List.append_nil, List.map_id, List.reverse_reverse]

    by_cases hk3 : k = src
    · subst k
      simp (disch := first | assumption | (apply Ne.symm; assumption)) only
        [S₃, S₂, S₁, movedR, Function.update_self, Function.update_of_ne,
          hc₁, hc₂, hc₃, List.append_nil, List.map_id, List.reverse_reverse,
          hsrc]
    by_cases hk4 : k = acc
    · subst k
      simp (disch := first | assumption | (apply Ne.symm; assumption)) only
        [S₃, S₂, S₁, movedR, Function.update_self, Function.update_of_ne,
          hc₁, hc₂, hc₃, List.append_nil, List.map_id, List.reverse_reverse]

    by_cases hk5 : k = savedSource
    · subst k
      simp (disch := first | assumption | (apply Ne.symm; assumption)) only
        [S₃, S₂, S₁, movedR, Function.update_self, Function.update_of_ne,
          hc₁, hc₂, hc₃, List.append_nil, List.map_id, List.reverse_reverse]

    ·
      simp (disch := first | assumption | (apply Ne.symm; assumption)) only
        [S₃, S₂, S₁, movedR, Function.update_self, Function.update_of_ne,
          hc₁, hc₂, hc₃, List.append_nil, List.map_id, List.reverse_reverse]


end IntegerMultBounds.MathlibTM2.Mult.ShortConv
