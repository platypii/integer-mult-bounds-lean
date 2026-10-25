module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpReverseRows

/-! # In-place coefficient-row reversal for the phase-cell upper stage

Reverse each row into scratch, replace the original stream, then return all
scratch to its initial empty state. Two symbol moves preserve coefficient bit
order. Applying this operation again restores the original rows.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Counts are retained. Only the exact coefficient-row source stream changes. -/
def reverseRowsInPlace
    (batch batchSaved rowCount recordSaved wordR recordSymbols src acc current savedSource saved buf tmp dst : Fin T) :
    Pr P T Q A U :=
  .seq (reverseRows batch batchSaved rowCount recordSaved wordR recordSymbols
    src acc current savedSource saved buf tmp dst)
    (.seq (uclear src) (.seq (moveR dst acc id) (moveR acc src id)))

/-- Reversal is executed and priced; no reversed operand is supplied by the caller. -/
theorem reverseRowsInPlace_exec
    {dst batch batchSaved rowCount recordSaved wordR recordSymbols src acc current savedSource saved buf tmp : Fin T}
    (hreg : [dst, batch, batchSaved, rowCount, recordSaved, wordR, recordSymbols, src,
      acc, current, savedSource, saved, buf, tmp].Nodup)
    (w r : ℕ) (blocks : List (List GaussianInt)) (hlen : ∀ xs ∈ blocks, xs.length = r)
    (v : HS T Q A U) (S : Stacks T A)
    (hbatch : (S.R batch).length = blocks.length)
    (hsrc : S.R src = cstream A w blocks.flatten)
    (hrow : (S.R rowCount).length = r) (hw : (S.R wordR).length = w)
    (hrecord : (S.R recordSymbols).length = r * w)
    (hclean : ∀ k ∈ [dst, batchSaved, acc, savedSource, recordSaved, current, saved, buf, tmp], S.R k = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (reverseRowsInPlace batch batchSaved rowCount recordSaved wordR recordSymbols
        src acc current savedSource saved buf tmp dst) (mk v S)
        (blocks.length * (32 * r * w + 19 * r + 17) + 14)
        (mk v' { S with R := (Function.update S.R src
          (cstream A w (blocks.flatMap List.reverse))) }) := by
  have hreg' := hreg
  regs_ne hreg'
  have hsd : src ≠ dst := ‹dst ≠ src›.symm
  have had : acc ≠ dst := ‹dst ≠ acc›.symm
  have has : acc ≠ src := ‹src ≠ acc›.symm
  have hdst : S.R dst = [] := hclean dst (by simp)
  have hacc : S.R acc = [] := hclean acc (by simp)
  obtain ⟨v₁, hu₁, he₁⟩ := reverseRows_exec (body := body) hreg w r blocks hlen v S [] hbatch
    (by simpa using hsrc) hrow hw hrecord (fun k hk => hclean k (by simp_all))
  let ys := cstream A w (blocks.flatMap List.reverse)
  let S₁ : Stacks T A := { S with R := Function.update S.R dst ys }
  have he₁' : Exec body (reverseRows batch batchSaved rowCount recordSaved wordR recordSymbols
      src acc current savedSource saved buf tmp dst) (mk v S)
      (blocks.length * (26 * r * w + 19 * r + 17) + 8) (mk v₁ S₁) := by
    simpa only [hdst, List.append_nil] using he₁
  obtain ⟨v₂, hu₂, he₂⟩ := uclear_exec (body := body) src v₁ S₁
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R src [] }
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body dst acc ‹dst ≠ acc› id v₂ S₂
  let S₃ : Stacks T A := { S₂ with R := movedR S₂.R dst acc id (S₂.R dst) }
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body acc src ‹src ≠ acc›.symm id v₃ S₃
  have hflat := reverseRows_flatten_length r blocks hlen
  have hxs : (cstream A w blocks.flatten).length = blocks.length * r * w := by
    rw [length_cstream, hflat]
  have hys : ys.length = blocks.length * r * w := by
    dsimp only [ys]
    rw [length_cstream]
    have hrev : (blocks.flatMap List.reverse).length = blocks.flatten.length := by
      simp only [List.length_flatMap, List.length_reverse, List.length_flatten]
    rw [hrev, hflat]
  refine ⟨v₄, hu₄.trans (hu₃.trans (hu₂.trans hu₁)),
    (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃ he₄))).cast ?_ ?_⟩
  · simp only [S₃, S₂, S₁, movedR, Function.update_self,
      Function.update_of_ne ‹src ≠ dst›, Function.update_of_ne ‹dst ≠ src›,
      Function.update_of_ne ‹acc ≠ dst›, Function.update_of_ne ‹acc ≠ src›,
      hacc, List.map_id, List.append_nil, List.length_reverse, hsrc, hxs, hys]
    ring
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hks : k = src
    · subst k
      simp [S₃, S₂, S₁, movedR, ys, hacc, ‹src ≠ dst›, ‹dst ≠ src›,
        ‹src ≠ acc›, ‹acc ≠ src›, ‹acc ≠ dst›]
    · by_cases hkd : k = dst
      · subst k
        simp [S₃, S₂, S₁, movedR, hdst, hacc, ‹dst ≠ src›,
          ‹dst ≠ acc›, ‹acc ≠ dst›, ‹acc ≠ src›]
      · by_cases hka : k = acc
        · subst k
          simp [S₃, S₂, S₁, movedR, hacc, ‹acc ≠ src›, ‹acc ≠ dst›]
        · simp [S₃, S₂, S₁, movedR, hks, hkd, hka]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
