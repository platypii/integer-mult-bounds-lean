module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRingRelease

/-! # Publish compact rows after releasing both padded product streams -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Release each padded batch, then use two moves to preserve compact symbol order. -/
def publishPairResult (lR width skip ringSymbols batch count src saved buf tmp compact acc : Fin T) :
    Pr P T Q A U :=
  .seq (releaseRingBatch lR width skip ringSymbols batch count src saved buf tmp)
    (.seq (releaseRingBatch lR width skip ringSymbols batch count src saved buf tmp)
      (.seq (moveR compact acc id) (moveR acc src id)))

/-- Only the persistent output and the consumed compact workspace change. Both
counter sets, all other work ports, and the arbitrary original suffix are exact. -/
theorem publishPairResult_exec
    {lR width skip ringSymbols batch count src saved buf tmp compact acc : Fin T}
    (hreg : [lR, width, skip, ringSymbols, batch, count, src, saved, buf, tmp, compact, acc].Nodup)
    (l w M : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (xs ys zs tail : List (Fin (A + 4)))
    (hl : (S.R lR).length = l) (hw : (S.R width).length = w) (hM : (S.R batch).length = M)
    (hsrc : S.R src = xs ++ (ys ++ tail))
    (hx : xs.length = M * (2 ^ l * w)) (hy : ys.length = M * (2 ^ l * w))
    (hz : S.R compact = zs)
    (hclean : ∀ k ∈ [skip, ringSymbols, count, saved, buf, tmp, acc], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 2 * (12 * (M * (2 ^ l * w)) + 9 * M + 4 * w + 6 * (2 ^ l * w) + 9 * l + 26) +
        4 * zs.length + 4 ∧
      Exec body (publishPairResult lR width skip ringSymbols batch count src saved buf tmp compact acc)
        (mk v S) n (mk v' { S with R := (Function.update (Function.update S.R compact []) src (zs ++ tail)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  have hr : [lR, width, skip, ringSymbols, batch, count, src, saved, buf, tmp].Nodup := by simp_all
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := releaseRingBatch_exec (body := body) hr l w M v S xs (ys ++ tail)
    hl hw hM hsrc hx (hclean _ (by simp)) (hclean _ (by simp)) (hclean _ (by simp))
    (hclean _ (by simp)) (hclean _ (by simp)) (hclean _ (by simp))
  let S₁ : Stacks T A := { S with R := Function.update S.R src (ys ++ tail) }
  have off₁ (k : Fin T) (hk : k ≠ src) : S₁.R k = S.R k := by simp [S₁, hk]
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := releaseRingBatch_exec (body := body) hr l w M v₁ S₁ ys tail
    (by rw [off₁ _ ‹lR ≠ src›]; exact hl)
    (by rw [off₁ _ ‹width ≠ src›]; exact hw)
    (by rw [off₁ _ ‹batch ≠ src›]; exact hM) (by simp [S₁]) hy
    (by rw [off₁ _ ‹skip ≠ src›]; exact hclean _ (by simp))
    (by rw [off₁ _ ‹ringSymbols ≠ src›]; exact hclean _ (by simp))
    (by rw [off₁ _ ‹count ≠ src›]; exact hclean _ (by simp))
    (by rw [off₁ _ ‹src ≠ saved›.symm]; exact hclean _ (by simp))
    (by rw [off₁ _ ‹src ≠ buf›.symm]; exact hclean _ (by simp))
    (by rw [off₁ _ ‹src ≠ tmp›.symm]; exact hclean _ (by simp))
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R src tail }
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body compact acc ‹compact ≠ acc› id v₂ S₂
  let S₃ : Stacks T A := { S₂ with R := movedR S₂.R compact acc id (S₂.R compact) }
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body acc src ‹src ≠ acc›.symm id v₃ S₃
  have hcompact : S₂.R compact = zs := by
    simp [S₂, S₁, ‹src ≠ compact›.symm, hz]
  have hacc : S₂.R acc = [] := by
    simp [S₂, S₁, ‹src ≠ acc›.symm, hclean _ (by simp : acc ∈ [skip, ringSymbols, count, saved, buf, tmp, acc])]
  have hacc₃ : S₃.R acc = zs.reverse := by simp [S₃, movedR, hcompact, hacc]
  refine ⟨v₄, n₁ + (n₂ + ((2 * zs.length + 2) + (2 * zs.length + 2))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)), by omega, ?_⟩
  refine (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))).cast ?_ ?_
  · rw [hcompact, hacc₃, List.length_reverse]
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    clear he₁ he₂ he₃ he₄ hu₁ hu₂ hu₃ hu₄
    funext k
    simp only [S₃, S₂, S₁, movedR, Function.update_apply, List.map_id]
    split_ifs <;> subst_vars <;> simp_all

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
