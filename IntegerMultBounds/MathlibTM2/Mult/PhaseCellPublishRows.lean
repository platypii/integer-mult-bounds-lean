module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReverseRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrefixRelease

/-! # Publish reversed coefficient rows above a borrowed output suffix

The row reversal preserves its source. Release only the counted old prefix,
then move the new stream back without reversing coefficient bits or the suffix.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def publishRows
    (batch batchSaved rows recordSaved width recordSymbols src acc current savedSource saved buf tmp dst count : Fin T) :
    Pr P T Q A U :=
  .seq (reverseRows batch batchSaved rows recordSaved width recordSymbols src acc current savedSource saved buf tmp dst)
    (.seq (releaseFromDimensions batch recordSymbols count src acc current tmp)
      (.seq (moveR dst acc id) (moveR acc src id)))

theorem publishRows_exec
    {dst batch batchSaved rows recordSaved width recordSymbols src acc current savedSource saved buf tmp count : Fin T}
    (hreg : [dst, batch, batchSaved, rows, recordSaved, width, recordSymbols, src,
      acc, current, savedSource, saved, buf, tmp, count].Nodup)
    (w L : ℕ) (blocks : List (List GaussianInt)) (hlen : ∀ xs ∈ blocks, xs.length = L)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A + 4)))
    (hbatch : (S.R batch).length = blocks.length)
    (hsrc : S.R src = cstream A w blocks.flatten ++ tail)
    (hrows : (S.R rows).length = L) (hwidth : (S.R width).length = w)
    (hrecord : (S.R recordSymbols).length = L * w)
    (hclean : ∀ k ∈ [dst, batchSaved, acc, savedSource, recordSaved, current, saved, buf, tmp, count], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ 42 * (blocks.length * L * w) + 19 * (blocks.length * L) + 26 * blocks.length + 24 ∧
      Exec body (publishRows batch batchSaved rows recordSaved width recordSymbols src acc current savedSource saved buf tmp dst count)
        (mk v S) m
        (mk v' { S with R := (Function.update S.R src
          (cstream A w (blocks.flatMap List.reverse) ++ tail)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  have hacc : S.R acc = [] := hclean acc (by simp)
  have hdst : S.R dst = [] := hclean dst (by simp)
  have hxs : (cstream A w blocks.flatten).length = blocks.length * L * w := by
    simp [reverseRows_flatten_length L blocks hlen]
  let ys := cstream A w (blocks.flatMap List.reverse)
  have hys : ys.length = blocks.length * L * w := by
    have hh : (blocks.flatMap List.reverse).length = blocks.flatten.length := by
      simp only [List.length_flatMap, List.length_reverse, List.length_flatten]
    simp [ys, hh, reverseRows_flatten_length L blocks hlen]
  obtain ⟨v₁, hu₁, he₁⟩ := reverseRows_exec (body := body)
    (show [dst, batch, batchSaved, rows, recordSaved, width, recordSymbols, src,
      acc, current, savedSource, saved, buf, tmp].Nodup by simp_all)
    w L blocks hlen v S tail hbatch hsrc hrows hwidth hrecord
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hclean _ (by simp))
  let S₁ : Stacks T A := { S with R := Function.update S.R dst ys }
  have he₁' : Exec body (reverseRows batch batchSaved rows recordSaved width recordSymbols src acc current savedSource saved buf tmp dst)
      (mk v S) (blocks.length * (26 * L * w + 19 * L + 17) + 8) (mk v₁ S₁) := by
    simpa only [hdst, List.append_nil] using he₁
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := releaseFromDimensions_exec (body := body)
    (show [batch, recordSymbols, count, src, acc, current, tmp].Nodup by simp_all [ne_comm])
    v₁ S₁ (cstream A w blocks.flatten) tail
    (by simpa [S₁, ‹dst ≠ src›.symm] using hsrc)
    (by simp [S₁, ‹dst ≠ batch›.symm, ‹dst ≠ recordSymbols›.symm, hbatch, hrecord, hxs, Nat.mul_assoc])
    (by simpa [S₁, ‹dst ≠ count›.symm] using hclean count (by simp))
    (by simpa [S₁, ‹dst ≠ acc›.symm] using hacc)
    (by simpa [S₁, ‹dst ≠ current›.symm] using hclean current (by simp))
    (by simpa [S₁, ‹dst ≠ tmp›.symm] using hclean tmp (by simp))
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R src tail }
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body dst acc ‹dst ≠ acc› id v₂ S₂
  let S₃ : Stacks T A := { S₂ with R := movedR S₂.R dst acc id (S₂.R dst) }
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body acc src ‹src ≠ acc›.symm id v₃ S₃
  have hdstlen : (S₂.R dst).length = blocks.length * L * w := by simp [S₂, S₁, ‹dst ≠ src›, hys]
  have hacclen : (S₃.R acc).length = blocks.length * L * w := by
    simp (disch := first | assumption | (apply Ne.symm; assumption)) [S₃, S₂, S₁, movedR, hacc, hys]
  refine ⟨v₄, (blocks.length * (26 * L * w + 19 * L + 17) + 8) +
    (m₂ + ((2 * (blocks.length * L * w) + 2) + (2 * (blocks.length * L * w) + 2))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_, ?_⟩
  · simp only [hxs, S₁, Function.update_of_ne ‹dst ≠ batch›.symm, hbatch] at hm₂
    nlinarith only [hm₂]
  · refine (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃ he₄))).cast (by rw [hdstlen, hacclen]) ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hs : k = src
    · subst k
      simp (disch := first | assumption | (apply Ne.symm; assumption)) [S₃, S₂, S₁, movedR, ys, hacc]
    · by_cases hd : k = dst
      · subst k
        simp (disch := first | assumption | (apply Ne.symm; assumption)) [S₃, S₂, S₁, movedR, hdst, hacc]
      · by_cases ha : k = acc
        · subst k
          simp (disch := first | assumption | (apply Ne.symm; assumption)) [S₃, S₂, S₁, movedR, hacc]
        · simp (disch := first | assumption | (apply Ne.symm; assumption)) [S₃, S₂, S₁, movedR]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
