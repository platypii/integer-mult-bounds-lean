module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrefixRelease
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefix

/-! # Install the next column and release its temporary output

One generated symbol count pays for erasing the owned old column prefix and
moving the next column into its place. Both borrowed suffixes restore exactly.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def replaceColumn (rows width count src next buf tmp : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct rows width count buf tmp)
    (.seq (releasePrefix count src buf tmp) (.seq (takePrefix count next src buf tmp) (uclear count)))

theorem replaceColumn_exec {rows width count src next buf tmp : Fin T}
    (hreg : [rows, width, count, src, next, buf, tmp].Nodup)
    (L W : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (xs ys tailX tailY : List (Fin (A + 4)))
    (hrows : (S.R rows).length = L) (hwidth : (S.R width).length = W)
    (hx : S.R src = xs ++ tailX) (hy : S.R next = ys ++ tailY)
    (hxlen : xs.length = L * W) (hylen : ys.length = L * W)
    (hcount : S.R count = []) (hbuf : S.R buf = []) (htmp : S.R tmp = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 18 * (L * W) + 9 * L + 18 ∧
      Exec body (replaceColumn rows width count src next buf tmp) (mk v S) m
        (mk v' { S with R := (Function.update (Function.update S.R src (ys ++ tailX)) next tailY) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := unaryProduct_exec (body := body)
    (show [rows, width, count, buf, tmp].Nodup by regs_nodup) v S hbuf htmp
  let S₁ : Stacks T A := { S with R := Function.update S.R count (List.replicate (L * W) tick) }
  have he₁' : Exec body (unaryProduct rows width count buf tmp) (mk v S) m₁ (mk v₁ S₁) := by
    simpa only [hrows, hwidth, hcount, List.append_nil] using he₁
  obtain ⟨v₂, hu₂, he₂⟩ := releasePrefix_exec (body := body)
    (show [count, src, buf, tmp].Nodup by regs_nodup) v₁ S₁ xs tailX
    (by simpa [S₁, ‹count ≠ src›.symm] using hx) (by simp [S₁, hxlen])
    (by simpa [S₁, ‹count ≠ buf›.symm] using hbuf)
    (by simpa [S₁, ‹count ≠ tmp›.symm] using htmp)
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R src tailX }
  obtain ⟨v₃, hu₃, he₃⟩ := takePrefix_exec (body := body)
    (show [count, next, src, buf, tmp].Nodup by regs_nodup) v₂ S₂ ys tailY
    (by simpa [S₂, S₁, ‹src ≠ next›.symm, ‹count ≠ next›.symm] using hy)
    (by simp [S₂, S₁, ‹count ≠ src›, hylen])
    (by simpa [S₂, S₁, ‹src ≠ buf›.symm, ‹count ≠ buf›.symm] using hbuf)
    (by simpa [S₂, S₁, ‹src ≠ tmp›.symm, ‹count ≠ tmp›.symm] using htmp)
  let S₃ : Stacks T A := { S₂ with R := (Function.update (Function.update S₂.R next tailY) src (ys ++ S₂.R src)) }
  obtain ⟨v₄, hu₄, he₄⟩ := uclear_exec body count v₃ S₃
  have hc₃ : (S₃.R count).length = L * W := by
    simp [S₃, S₂, S₁, ‹count ≠ src›, ‹count ≠ next›]
  refine ⟨v₄, m₁ + ((6 * (L * W) + 6) + ((6 * (L * W) + 6) + (2 * (L * W) + 2))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_, ?_⟩
  · rw [hrows, hwidth] at hm₁
    nlinarith only [hm₁]
  · refine (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃ he₄))).cast (by rw [hxlen, hylen, hc₃]) ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hc : k = count
    · subst k
      simp [hcount, ‹count ≠ src›, ‹count ≠ next›]
    by_cases hs : k = src
    · subst k
      simp [S₃, S₂, S₁, ‹count ≠ src›.symm, ‹src ≠ next›]
    by_cases hn : k = next
    · subst k
      simp [S₃, ‹src ≠ next›.symm, ‹count ≠ next›.symm]
    simp [S₃, S₂, S₁, hc, hs, hn]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
