module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpExtract
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! # Correlation extraction from unary dimensions

Generate the skip count `3mw` from the actual unary dimensions, extract whole words,
and clear both generated counters. No prepared skip word is supplied by the caller.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Prepare `3m` and `3mw`, extract, then release the two generated words. -/
def correlationFromUnary (mR wR triples skip savedSkip recordSaved src dst saved buf tmp : Fin T) :
    Pr P T Q A U :=
  .seq (umulSym 3 tick mR triples tmp) <|
  .seq (unaryProduct triples wR skip buf tmp) <|
  .seq (reverseSlice skip savedSkip mR recordSaved wR src dst saved buf tmp) <|
  .seq (uclear skip) (uclear triples)

/-- The complete extraction phase preserves its source, dimensions, suffix and workspace. -/
theorem correlationFromUnary_exec
    {mR wR triples skip savedSkip recordSaved src dst saved buf tmp : Fin T}
    (hreg : [mR, wR, triples, skip, savedSkip, recordSaved, src, dst, saved, buf, tmp].Nodup)
    (m w : ℕ) (xs : List GaussianInt) (hsize : 4 * m ≤ xs.length)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A + 4)))
    (hm : (S.R mR).length = m) (hw : (S.R wR).length = w)
    (hsrc : S.R src = cstream A w xs ++ tail)
    (htriples : S.R triples = []) (hskip : S.R skip = [])
    (hsavedSkip : S.R savedSkip = []) (hrecordSaved : S.R recordSaved = [])
    (hsaved : S.R saved = []) (hbuf : S.R buf = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 52 * m * w + 56 * m + 24 ∧
      Exec body (correlationFromUnary mR wR triples skip savedSkip recordSaved src dst saved buf tmp)
        (mk v S) n
        (mk v' { S with R := (Function.update S.R dst
          (cstream A w (correlationCoeffs m xs) ++ S.R dst)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := umulSym_exec (body := body) 3 tick ‹mR ≠ triples› ‹mR ≠ tmp›
    ‹triples ≠ tmp› v S htmp
  rw [hm, htriples, List.append_nil] at he₁
  set S₁ : Stacks T A := { S with R := Function.update S.R triples (List.replicate (3 * m) tick) }
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := unaryProduct_exec (body := body)
    (show [triples, wR, skip, buf, tmp].Nodup by simp_all [ne_comm]) v₁ S₁
    (by simp [S₁, ‹triples ≠ buf›.symm, hbuf])
    (by simp [S₁, ‹triples ≠ tmp›.symm, htmp])
  have hlen : (S₁.R triples).length = 3 * m := by simp [S₁]
  have hw₁ : (S₁.R wR).length = w := by simpa [S₁, ‹wR ≠ triples›] using hw
  have hskip₁ : S₁.R skip = [] := by simp [S₁, ‹triples ≠ skip›.symm, hskip]
  rw [hlen, hw₁] at hn₂ he₂
  rw [hskip₁, List.append_nil] at he₂
  set S₂ : Stacks T A := { S₁ with R := (Function.update S₁.R skip
    (List.replicate (3 * m * w) tick)) }
  have e (r : Fin T) (ht : r ≠ triples) (hs : r ≠ skip) : S₂.R r = S.R r := by
    simp [S₂, S₁, ht, hs]
  obtain ⟨v₃, hu₃, he₃⟩ := correlationCoeffs_exec (body := body)
    (show [skip, savedSkip, mR, recordSaved, wR, src, dst, saved, buf, tmp].Nodup by
      simp_all [ne_comm]) w m xs hsize v₂ S₂ tail
    (by rw [e _ ‹triples ≠ src›.symm ‹skip ≠ src›.symm]; exact hsrc)
    (by simp [S₂])
    (by rw [e _ ‹mR ≠ triples› ‹mR ≠ skip›]; exact hm)
    (by rw [e _ ‹wR ≠ triples› ‹wR ≠ skip›]; exact hw)
    (by rw [e _ ‹triples ≠ savedSkip›.symm ‹skip ≠ savedSkip›.symm]; exact hsavedSkip)
    (by rw [e _ ‹triples ≠ recordSaved›.symm ‹skip ≠ recordSaved›.symm]; exact hrecordSaved)
    (by rw [e _ ‹triples ≠ saved›.symm ‹skip ≠ saved›.symm]; exact hsaved)
    (by rw [e _ ‹triples ≠ buf›.symm ‹skip ≠ buf›.symm]; exact hbuf)
    (by rw [e _ ‹triples ≠ tmp›.symm ‹skip ≠ tmp›.symm]; exact htmp)
  set S₃ : Stacks T A := { S₂ with R := (Function.update S₂.R dst
    (cstream A w (correlationCoeffs m xs) ++ S₂.R dst)) }
  obtain ⟨v₄, hu₄, he₄⟩ := uclear_exec body skip v₃ S₃
  set S₄ : Stacks T A := { S₃ with R := Function.update S₃.R skip [] }
  obtain ⟨v₅, hu₅, he₅⟩ := uclear_exec body triples v₄ S₄
  refine ⟨v₅, _, hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), ?_,
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))).cast rfl ?_⟩
  · have hskip₃ : (S₃.R skip).length = 3 * m * w := by simp [S₃, S₂, ‹skip ≠ dst›]
    have htriples₄ : (S₄.R triples).length = 3 * m := by
      simp [S₄, S₃, S₂, S₁, ‹triples ≠ skip›, ‹triples ≠ dst›]
    rw [hskip₃, htriples₄]
    nlinarith [hn₂]
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    clear he₁ he₂ he₃ he₄ he₅ hu₁ hu₂ hu₃ hu₄ hu₅ e
    funext r
    simp only [S₄, S₃, S₂, S₁, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
