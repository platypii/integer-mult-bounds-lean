module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHalfCount

/-! # Generate ML from the retained 2M and L headers -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Recover M, form ML, then release M. The doubled header is restored. -/
def branchWords (batch saved half rows words buf tmp : Fin T) : Pr P T Q A U :=
  .seq (halfCount batch saved half)
    (.seq (unaryProduct half rows words buf tmp) (uclear half))

theorem branchWords_exec {batch saved half rows words buf tmp : Fin T}
    (hreg : [batch, saved, half, rows, words, buf, tmp].Nodup)
    (M L : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hbatch : (S.R batch).length = 2 * M) (hrows : (S.R rows).length = L)
    (hclean : ∀ k ∈ [saved, half, words, buf, tmp], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 4 * (M * L) + 17 * M + 10 ∧
      Exec body (branchWords batch saved half rows words buf tmp) (mk v S) m
        (mk v' { S with R := Function.update S.R words (List.replicate (M * L) tick) }) := by
  have hreg' := hreg
  regs_ne hreg'
  have hh : S.R half = [] := hclean half (by simp)
  have hw : S.R words = [] := hclean words (by simp)
  obtain ⟨v₁, hu₁, he₁⟩ := halfCount_exec (body := body)
    (show [batch, saved, half].Nodup by simp_all) M v S hbatch (hclean _ (by simp))
  let S₁ : Stacks T A := { S with R := Function.update S.R half (List.replicate M tick) }
  have he₁' : Exec body (halfCount batch saved half) (mk v S) (6 * M + 4) (mk v₁ S₁) := by
    simpa only [hh, List.append_nil] using he₁
  have off (k : Fin T) (hk : k ≠ half) : S₁.R k = S.R k := by simp [S₁, hk]
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := unaryProduct_exec (body := body)
    (show [half, rows, words, buf, tmp].Nodup by simp_all) v₁ S₁
    (by rw [off _ ‹half ≠ buf›.symm]; exact hclean _ (by simp))
    (by rw [off _ ‹half ≠ tmp›.symm]; exact hclean _ (by simp))
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R words (List.replicate (M * L) tick) }
  have he₂' : Exec body (unaryProduct half rows words buf tmp) (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa only [S₁, Function.update_self, List.length_replicate,
      Function.update_of_ne ‹half ≠ rows›.symm, Function.update_of_ne ‹half ≠ words›.symm,
      hrows, hw, List.append_nil] using he₂
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body half v₂ S₂
  have hc : (S₂.R half).length = M := by simp [S₂, S₁, ‹half ≠ words›]
  refine ⟨v₃, (6 * M + 4) + (m₂ + (2 * M + 2)), hu₃.trans (hu₂.trans hu₁), ?_, ?_⟩
  · simp only [S₁, Function.update_self, List.length_replicate,
      Function.update_of_ne ‹half ≠ rows›.symm, hrows] at hm₂
    nlinarith only [hm₂]
  · refine (Exec.seq he₁' (Exec.seq he₂' he₃)).cast (by rw [hc]) ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hk : k = half
    · subst k
      simp [S₂, S₁, hh, ‹half ≠ words›]
    · by_cases hw' : k = words
      · subst k
        simp [S₂, S₁, hk]
      · simp [S₂, S₁, hk, hw']

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
