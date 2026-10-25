module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! # Copy a retained square factor page with generated counts

Both row counts and the word width are ordinary retained headers. The square
word count and symbol count are generated and released; source suffixes restore.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def copyFactorPage (rows rowCount width square count src dst saved tmp : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct rows rowCount square saved tmp)
    (.seq (unaryProduct square width count saved tmp)
      (.seq (copyPrefix count src dst saved tmp) (.seq (uclear count) (uclear square))))

theorem copyFactorPage_exec {rows rowCount width square count src dst saved tmp : Fin T}
    (hreg : [rows, rowCount, width, square, count, src, dst, saved, tmp].Nodup)
    (L W : ℕ) (v : HS T Q A U) (S : Stacks T A) (xs tail : List (Fin (A + 4)))
    (hrows : (S.R rows).length = L) (hrowCount : (S.R rowCount).length = L)
    (hwidth : (S.R width).length = W) (hsrc : S.R src = xs ++ tail) (hlen : xs.length = L * L * W)
    (hsquare : S.R square = []) (hcount : S.R count = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 16 * (L * L * W) + 15 * (L * L) + 9 * L + 22 ∧
      Exec body (copyFactorPage rows rowCount width square count src dst saved tmp) (mk v S) m
        (mk v' { S with R := Function.update S.R dst (xs ++ S.R dst) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := unaryProduct_exec (body := body)
    (show [rows, rowCount, square, saved, tmp].Nodup by regs_nodup) v S hsaved htmp
  let S₁ : Stacks T A := { S with R := Function.update S.R square (List.replicate (L * L) tick) }
  have he₁' : Exec body (unaryProduct rows rowCount square saved tmp) (mk v S) m₁ (mk v₁ S₁) := by
    simpa only [hrows, hrowCount, hsquare, List.append_nil] using he₁
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := unaryProduct_exec (body := body)
    (show [square, width, count, saved, tmp].Nodup by regs_nodup) v₁ S₁
    (by simpa [S₁, ‹square ≠ saved›.symm] using hsaved)
    (by simpa [S₁, ‹square ≠ tmp›.symm] using htmp)
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R count (List.replicate (L * L * W) tick) }
  have hs₁ : (S₁.R square).length = L * L := by simp [S₁]
  have hw₁ : (S₁.R width).length = W := by simpa [S₁, ‹width ≠ square›] using hwidth
  have he₂' : Exec body (unaryProduct square width count saved tmp) (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa [S₂, hs₁, hw₁, S₁, ‹square ≠ count›.symm, hcount] using he₂
  obtain ⟨v₃, hu₃, he₃⟩ := copyPrefix_exec (body := body)
    (show [count, src, dst, saved, tmp].Nodup by regs_nodup) v₂ S₂ xs tail
    (by simpa [S₂, S₁, ‹count ≠ src›.symm, ‹square ≠ src›.symm] using hsrc)
    (by simp [S₂, hlen])
    (by simpa [S₂, S₁, ‹count ≠ saved›.symm, ‹square ≠ saved›.symm] using hsaved)
    (by simpa [S₂, S₁, ‹count ≠ tmp›.symm, ‹square ≠ tmp›.symm] using htmp)
  let S₃ : Stacks T A := { S₂ with R := Function.update S₂.R dst (xs ++ S₂.R dst) }
  obtain ⟨v₄, hu₄, he₄⟩ := uclear_exec body count v₃ S₃
  let S₄ : Stacks T A := { S₃ with R := Function.update S₃.R count [] }
  obtain ⟨v₅, hu₅, he₅⟩ := uclear_exec body square v₄ S₄
  have hc₃ : (S₃.R count).length = L * L * W := by simp [S₃, S₂, ‹count ≠ dst›]
  have hs₄ : (S₄.R square).length = L * L := by
    simp [S₄, S₃, S₂, S₁, ‹square ≠ count›, ‹square ≠ dst›]
  refine ⟨v₅, m₁ + (m₂ + ((10 * (L * L * W) + 10) + ((2 * (L * L * W) + 2) + (2 * (L * L) + 2)))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), ?_, ?_⟩
  · rw [hrows, hrowCount] at hm₁
    rw [hs₁, hw₁] at hm₂
    nlinarith only [hm₁, hm₂]
  · refine (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄ he₅)))).cast
      (by rw [hlen, hc₃, hs₄]) ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hs : k = square
    · subst k; simp [hsquare, ‹square ≠ dst›]
    by_cases hc : k = count
    · subst k; simp [S₄, ‹square ≠ count›.symm, ‹count ≠ dst›, hcount]
    by_cases hd : k = dst
    · subst k; simp [S₄, S₃, S₂, S₁, ‹count ≠ dst›.symm, ‹square ≠ dst›.symm]
    simp [S₄, S₃, S₂, S₁, hs, hc, hd]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
