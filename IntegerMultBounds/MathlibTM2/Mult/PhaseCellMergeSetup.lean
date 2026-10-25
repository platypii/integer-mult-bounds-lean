module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMergePublish
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! # Generated count and cleanup around the routed branch merge -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Generate the total symbol count, merge both branches, release the count. -/
def mergeFromWords (words width count src a b acc buf tmp : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct words width count buf tmp)
    (.seq (mergePair count src a b acc width buf tmp) (uclear count))

/-- Starting with a word-count header, the entire routed merge executes with no
supplied product counter. All counters and work stacks are restored exactly. -/
theorem mergeFromWords_exec {words width count src a b acc buf tmp : Fin T}
    (hreg : [words, width, count, src, a, b, acc, buf, tmp].Nodup) (hA : 96 ≤ A)
    {w n : ℕ} (hw : 1 ≤ w) (X Y : Fin n → GaussianInt)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A + 4)))
    (hwords : (S.R words).length = n) (hwidth : (S.R width).length = w)
    (hsrc : S.R src = cstream A w (List.ofFn X) ++ (cstream A w (List.ofFn Y) ++ tail))
    (hclean : ∀ k ∈ [count, a, b, acc, buf, tmp], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ n * (25 * w + 15) + 22 ∧
      Exec body (mergeFromWords words width count src a b acc buf tmp) (mk v S) m
        (mk v' { S with R := (Function.update S.R src
          (cstream A w (List.ofFn (fun i => X i - Y i)) ++ tail)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  have hc : S.R count = [] := hclean count (by simp)
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := unaryProduct_exec (body := body)
    (show [words, width, count, buf, tmp].Nodup by simp_all) v S
    (hclean _ (by simp)) (hclean _ (by simp))
  let S₁ : Stacks T A := { S with R := Function.update S.R count (List.replicate (n * w) tick) }
  have he₁' : Exec body (unaryProduct words width count buf tmp) (mk v S) m₁ (mk v₁ S₁) := by
    simpa only [hwords, hwidth, hc, List.append_nil] using he₁
  have off (k : Fin T) (hk : k ≠ count) : S₁.R k = S.R k := by simp [S₁, hk]
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := mergePair_exec (body := body)
    (show [count, src, a, b, acc, width, buf, tmp].Nodup by simp_all [ne_comm]) hA hw X Y v₁ S₁ tail
    (by rw [off _ ‹count ≠ src›.symm]; exact hsrc) (by simp [S₁])
    (by rw [off _ ‹width ≠ count›]; exact hwidth)
    (by
      intro k hk
      have hne : k ≠ count := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl
        all_goals first | assumption | (apply Ne.symm; assumption)
      rw [off k hne]
      exact hclean k (List.mem_cons_of_mem count hk))
  let S₂ : Stacks T A := { S₁ with R := (Function.update S₁.R src
    (cstream A w (List.ofFn (fun i => X i - Y i)) ++ tail)) }
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body count v₂ S₂
  have hcount : (S₂.R count).length = n * w := by simp [S₂, S₁, ‹count ≠ src›]
  refine ⟨v₃, m₁ + (m₂ + (2 * (n * w) + 2)), hu₃.trans (hu₂.trans hu₁), ?_, ?_⟩
  · rw [hwords, hwidth] at hm₁
    nlinarith only [hm₁, hm₂]
  · refine (Exec.seq he₁' (Exec.seq he₂ he₃)).cast (by rw [hcount]) ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hk : k = count
    · subst k
      simp [S₂, S₁, hc, ‹count ≠ src›]
    · by_cases hs : k = src
      · subst k
        simp [S₂, S₁, hk]
      · simp [S₂, S₁, hk, hs]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
