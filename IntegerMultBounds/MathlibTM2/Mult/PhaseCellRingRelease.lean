module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrefixRelease
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvPadding

/-! # Release a padded result batch from exponent and width headers -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Generate the ring-symbol and batch-total counts, remove one padded batch,
and release both counts. -/
def releaseRingBatch (lR width skip ringSymbols batch count src saved buf tmp : Fin T) : Pr P T Q A U :=
  .seq (padding lR width skip ringSymbols buf tmp)
    (.seq (releaseFromDimensions batch ringSymbols count src saved buf tmp) (uclear ringSymbols))

theorem releaseRingBatch_exec {lR width skip ringSymbols batch count src saved buf tmp : Fin T}
    (hreg : [lR, width, skip, ringSymbols, batch, count, src, saved, buf, tmp].Nodup)
    (l w M : ℕ) (v : HS T Q A U) (S : Stacks T A) (xs tail : List (Fin (A + 4)))
    (hl : (S.R lR).length = l) (hw : (S.R width).length = w) (hM : (S.R batch).length = M)
    (hsrc : S.R src = xs ++ tail) (hlen : xs.length = M * (2 ^ l * w))
    (hskip : S.R skip = []) (hring : S.R ringSymbols = []) (hcount : S.R count = [])
    (hsaved : S.R saved = []) (hbuf : S.R buf = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 12 * xs.length + 9 * M + 4 * w + 6 * (2 ^ l * w) + 9 * l + 26 ∧
      Exec body (releaseRingBatch lR width skip ringSymbols batch count src saved buf tmp) (mk v S) n
        (mk v' { S with R := Function.update S.R src tail }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := padding_exec (body := body)
    (show [lR, width, skip, ringSymbols, buf, tmp].Nodup by simp_all) v S hring hbuf htmp
  let S₁ : Stacks T A := { S with R := Function.update S.R ringSymbols (List.replicate (2 ^ l * w) tick) }
  have he₁' : Exec body (padding lR width skip ringSymbols buf tmp) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [hl, hw, hskip, List.length_nil, Nat.sub_zero] using he₁
  have off (k : Fin T) (hk : k ≠ ringSymbols) : S₁.R k = S.R k := by simp [S₁, hk]
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := releaseFromDimensions_exec (body := body)
    (show [batch, ringSymbols, count, src, saved, buf, tmp].Nodup by simp_all [ne_comm])
    v₁ S₁ xs tail (by rw [off _ ‹ringSymbols ≠ src›.symm]; exact hsrc)
    (by simpa [S₁, ‹ringSymbols ≠ batch›.symm, hM] using hlen)
    (by rw [off _ ‹ringSymbols ≠ count›.symm]; exact hcount)
    (by rw [off _ ‹ringSymbols ≠ saved›.symm]; exact hsaved)
    (by rw [off _ ‹ringSymbols ≠ buf›.symm]; exact hbuf)
    (by rw [off _ ‹ringSymbols ≠ tmp›.symm]; exact htmp)
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R src tail }
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body ringSymbols v₂ S₂
  have hc : (S₂.R ringSymbols).length = 2 ^ l * w := by simp [S₂, S₁, ‹ringSymbols ≠ src›]
  refine ⟨v₃, n₁ + (n₂ + (2 * (2 ^ l * w) + 2)), hu₃.trans (hu₂.trans hu₁), ?_, ?_⟩
  · rw [off _ ‹ringSymbols ≠ batch›.symm, hM] at hn₂
    rw [hl, hw, hskip] at hn₁
    simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at hn₁
    nlinarith only [hn₁, hn₂]
  · refine (Exec.seq he₁' (Exec.seq he₂ he₃)).cast (by rw [hc]) ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hk : k = ringSymbols
    · subst k
      simp [S₂, S₁, hring, ‹ringSymbols ≠ src›]
    · by_cases hs : k = src
      · subst k
        simp [S₂, S₁, hk]
      · simp [S₂, S₁, hk, hs]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
