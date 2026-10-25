module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReverseRows
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! # Generate and release the row-symbol count for the upper Toeplitz stage -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Generate L*w from the retained unary dimensions, reverse rows, and erase the generated count. -/
def reverseRowsFromDimensions
    (batch batchSaved rowCount recordSaved wordR recordSymbols src acc current savedSource saved buf tmp dst : Fin T) :
    Pr P T Q A U :=
  .seq (unaryProduct rowCount wordR recordSymbols buf tmp)
    (.seq (reverseRowsInPlace batch batchSaved rowCount recordSaved wordR recordSymbols
      src acc current savedSource saved buf tmp dst) (uclear recordSymbols))

/-- The preparation and its generated counter are paid; only the row source changes. -/
theorem reverseRowsFromDimensions_exec
    {dst batch batchSaved rowCount recordSaved wordR recordSymbols src acc current savedSource saved buf tmp : Fin T}
    (hreg : [dst, batch, batchSaved, rowCount, recordSaved, wordR, recordSymbols, src,
      acc, current, savedSource, saved, buf, tmp].Nodup)
    (w r : ℕ) (blocks : List (List GaussianInt)) (hlen : ∀ xs ∈ blocks, xs.length = r)
    (v : HS T Q A U) (S : Stacks T A)
    (hbatch : (S.R batch).length = blocks.length)
    (hsrc : S.R src = cstream A w blocks.flatten)
    (hrow : (S.R rowCount).length = r) (hw : (S.R wordR).length = w)
    (hclean : ∀ k ∈ [recordSymbols, dst, batchSaved, acc, savedSource, recordSaved, current, saved, buf, tmp],
      S.R k = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ blocks.length * (32 * r * w + 19 * r + 17) + 6 * r * w + 9 * r + 20 ∧
      Exec body (reverseRowsFromDimensions batch batchSaved rowCount recordSaved wordR recordSymbols
        src acc current savedSource saved buf tmp dst) (mk v S) n
        (mk v' { S with R := (Function.update S.R src
          (cstream A w (blocks.flatMap List.reverse))) }) := by
  have hreg' := hreg
  regs_ne hreg'
  have hc : S.R recordSymbols = [] := hclean recordSymbols (by simp)
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := unaryProduct_exec (body := body)
    (show [rowCount, wordR, recordSymbols, buf, tmp].Nodup by simp_all)
    v S (hclean buf (by simp)) (hclean tmp (by simp))
  let S₁ : Stacks T A := { S with R := Function.update S.R recordSymbols (List.replicate (r * w) tick) }
  have he₁' : Exec body (unaryProduct rowCount wordR recordSymbols buf tmp) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [hrow, hw, hc, List.append_nil] using he₁
  have off (k : Fin T) (hk : k ≠ recordSymbols) : S₁.R k = S.R k := by simp [S₁, hk]
  obtain ⟨v₂, hu₂, he₂⟩ := reverseRowsInPlace_exec (body := body) hreg w r blocks hlen v₁ S₁
    (by rw [off _ ‹batch ≠ recordSymbols›]; exact hbatch)
    (by rw [off _ ‹recordSymbols ≠ src›.symm]; exact hsrc)
    (by rw [off _ ‹rowCount ≠ recordSymbols›]; exact hrow)
    (by rw [off _ ‹wordR ≠ recordSymbols›]; exact hw)
    (by simp [S₁]) (by
      intro k hk
      have hne : k ≠ recordSymbols := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | assumption | (apply Ne.symm; assumption)
      rw [off k hne]
      exact hclean k (List.mem_cons_of_mem recordSymbols hk))
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R src (cstream A w (blocks.flatMap List.reverse)) }
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec (body := body) recordSymbols v₂ S₂
  have hlenCount : (S₂.R recordSymbols).length = r * w := by
    simp [S₂, S₁, ‹recordSymbols ≠ src›]
  refine ⟨v₃, n₁ + (blocks.length * (32 * r * w + 19 * r + 17) + 14 +
      (2 * (r * w) + 2)), hu₃.trans (hu₂.trans hu₁), ?_, ?_⟩
  · rw [hrow, hw] at hn₁
    nlinarith only [hn₁]
  · refine (Exec.seq he₁' (Exec.seq he₂ he₃)).cast (by rw [hlenCount]) ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hk : k = recordSymbols
    · subst k
      simp [S₂, S₁, hc, ‹recordSymbols ≠ src›]
    · by_cases hs : k = src
      · subst k
        simp [S₂, S₁, hk]
      · simp [S₂, S₁, hk, hs]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
