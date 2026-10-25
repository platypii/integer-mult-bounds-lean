module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! # Paid release of a counted temporary prefix

The suffix is arbitrary, and only the selected prefix is touched. Count generation
and release are explicit; the caller never supplies an execution or cleanup oracle.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Move exactly the counted prefix into fresh workspace, then erase it. -/
def releasePrefix (count src saved tmp : Fin T) : Pr P T Q A U :=
  .seq (transfer count src saved tmp) (uclear saved)

/-- Original count symbols, suffix and all other stacks survive, including empty prefixes. -/
theorem releasePrefix_exec {count src saved tmp : Fin T}
    (hreg : [count, src, saved, tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (xs tail : List (Fin (A + 4)))
    (hsrc : S.R src = xs ++ tail) (hlen : (S.R count).length = xs.length)
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (releasePrefix count src saved tmp) (mk v S) (6 * xs.length + 6)
        (mk v' { S with R := Function.update S.R src tail }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := transfer_exec (body := body) hreg v S xs tail hsrc hlen htmp
  let S₁ : Stacks T A := { S with R := (Function.update (Function.update S.R src tail)
    saved (xs.reverse ++ S.R saved)) }
  obtain ⟨v₂, hu₂, he₂⟩ := uclear_exec body saved v₁ S₁
  refine ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁ he₂).cast ?_ ?_⟩
  · simp [S₁, hsaved]
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hk : k = saved
    · subst k
      simp [S₁, hsaved, ‹src ≠ saved›.symm]
    · simp [S₁, hk]

/-- Generate the prefix count from two retained dimensions, erase the prefix and
release the generated count. -/
def releaseFromDimensions (a b count src saved buf tmp : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct a b count buf tmp)
    (.seq (releasePrefix count src saved tmp) (uclear count))

/-- Setup, prefix release and count cleanup are all charged; the borrowed suffix is exact. -/
theorem releaseFromDimensions_exec {a b count src saved buf tmp : Fin T}
    (hreg : [a, b, count, src, saved, buf, tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (xs tail : List (Fin (A + 4)))
    (hsrc : S.R src = xs ++ tail)
    (hlen : xs.length = (S.R a).length * (S.R b).length)
    (hcount : S.R count = []) (hsaved : S.R saved = [])
    (hbuf : S.R buf = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 12 * xs.length + 9 * (S.R a).length + 12 ∧
      Exec body (releaseFromDimensions a b count src saved buf tmp) (mk v S) n
        (mk v' { S with R := Function.update S.R src tail }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := unaryProduct_exec (body := body)
    (show [a, b, count, buf, tmp].Nodup by simp_all) v S hbuf htmp
  let S₁ : Stacks T A := { S with R := (Function.update S.R count
    (List.replicate xs.length tick)) }
  have he₁' : Exec body (unaryProduct a b count buf tmp) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [← hlen, hcount, List.append_nil] using he₁
  obtain ⟨v₂, hu₂, he₂⟩ := releasePrefix_exec (body := body)
    (show [count, src, saved, tmp].Nodup by simp_all) v₁ S₁ xs tail
    (by simpa [S₁, ‹count ≠ src›.symm] using hsrc)
    (by simp [S₁])
    (by simpa [S₁, ‹count ≠ saved›.symm] using hsaved)
    (by simpa [S₁, ‹count ≠ tmp›.symm] using htmp)
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R src tail }
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body count v₂ S₂
  have hc : (S₂.R count).length = xs.length := by simp [S₂, S₁, ‹count ≠ src›]
  refine ⟨v₃, n₁ + (6 * xs.length + 6 + (2 * xs.length + 2)),
    hu₃.trans (hu₂.trans hu₁), ?_, ?_⟩
  · nlinarith only [hn₁, hlen]
  · refine (Exec.seq he₁' (Exec.seq he₂ he₃)).cast (by rw [hc]) ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hk : k = count
    · subst k
      simp [S₂, S₁, hcount, ‹count ≠ src›]
    · by_cases hs : k = src
      · subst k
        simp [S₂, S₁, hk]
      · simp [S₂, S₁, hk, hs]

/-- Generate both symbols-per-row and total-symbol counts from retained dimensions. -/
def releaseRows (batch rows width rowSymbols count src saved buf tmp : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct rows width rowSymbols buf tmp)
    (.seq (releaseFromDimensions batch rowSymbols count src saved buf tmp) (uclear rowSymbols))

/-- Release a complete temporary batch without receiving either product counter. -/
theorem releaseRows_exec {batch rows width rowSymbols count src saved buf tmp : Fin T}
    (hreg : [batch, rows, width, rowSymbols, count, src, saved, buf, tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (xs tail : List (Fin (A + 4)))
    (hsrc : S.R src = xs ++ tail)
    (hlen : xs.length = (S.R batch).length * ((S.R rows).length * (S.R width).length))
    (hrowSymbols : S.R rowSymbols = []) (hcount : S.R count = [])
    (hsaved : S.R saved = []) (hbuf : S.R buf = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 12 * xs.length + 9 * (S.R batch).length +
        6 * ((S.R rows).length * (S.R width).length) + 9 * (S.R rows).length + 18 ∧
      Exec body (releaseRows batch rows width rowSymbols count src saved buf tmp) (mk v S) n
        (mk v' { S with R := Function.update S.R src tail }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := unaryProduct_exec (body := body)
    (show [rows, width, rowSymbols, buf, tmp].Nodup by simp_all) v S hbuf htmp
  let r := (S.R rows).length * (S.R width).length
  let S₁ : Stacks T A := { S with R := Function.update S.R rowSymbols (List.replicate r tick) }
  have he₁' : Exec body (unaryProduct rows width rowSymbols buf tmp) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [hrowSymbols, List.append_nil] using he₁
  have off (k : Fin T) (hk : k ≠ rowSymbols) : S₁.R k = S.R k := by simp [S₁, hk]
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := releaseFromDimensions_exec (body := body)
    (show [batch, rowSymbols, count, src, saved, buf, tmp].Nodup by simp_all)
    v₁ S₁ xs tail (by rw [off _ ‹rowSymbols ≠ src›.symm]; exact hsrc)
    (by simpa [S₁, r, ‹batch ≠ rowSymbols›] using hlen)
    (by rw [off _ ‹rowSymbols ≠ count›.symm]; exact hcount)
    (by rw [off _ ‹rowSymbols ≠ saved›.symm]; exact hsaved)
    (by rw [off _ ‹rowSymbols ≠ buf›.symm]; exact hbuf)
    (by rw [off _ ‹rowSymbols ≠ tmp›.symm]; exact htmp)
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R src tail }
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body rowSymbols v₂ S₂
  have hc : (S₂.R rowSymbols).length = r := by simp [S₂, S₁, ‹rowSymbols ≠ src›]
  refine ⟨v₃, n₁ + (n₂ + (2 * r + 2)), hu₃.trans (hu₂.trans hu₁), ?_, ?_⟩
  · rw [off _ ‹batch ≠ rowSymbols›] at hn₂
    dsimp only [r]
    nlinarith only [hn₁, hn₂]
  · refine (Exec.seq he₁' (Exec.seq he₂ he₃)).cast (by rw [hc]) ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hk : k = rowSymbols
    · subst k
      simp [S₂, S₁, hrowSymbols, ‹rowSymbols ≠ src›]
    · by_cases hs : k = src
      · subst k
        simp [S₂, S₁, hk]
      · simp [S₂, S₁, hk, hs]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
