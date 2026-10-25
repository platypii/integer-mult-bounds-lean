module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! # Copy a counted word behind a counted prefix, restoring the source exactly -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

def copyAfterPrefix (skip width src dst savedPrefix savedWord tmp : Fin T) : Pr P T Q A U :=
  .seq (transfer skip src savedPrefix tmp)
    (.seq (copyPrefix width src dst savedWord tmp) (moveR savedPrefix src id))

/-- Prefix and suffix symbols are arbitrary; only the copied destination prefix changes. -/
theorem copyAfterPrefix_exec {skip width src dst savedPrefix savedWord tmp : Fin T}
    (hreg : [skip, width, src, dst, savedPrefix, savedWord, tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (pre word tail : List (Fin (A + 4)))
    (hsrc : S.R src = pre ++ (word ++ tail))
    (hskip : (S.R skip).length = pre.length) (hwidth : (S.R width).length = word.length)
    (hpre : S.R savedPrefix = []) (hword : S.R savedWord = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (copyAfterPrefix skip width src dst savedPrefix savedWord tmp) (mk v S)
        (6 * pre.length + 10 * word.length + 16)
        (mk v' { S with R := Function.update S.R dst (word ++ S.R dst) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := transfer_exec (body := body)
    (show [skip, src, savedPrefix, tmp].Nodup by simp_all) v S pre (word ++ tail) hsrc hskip htmp
  let S₁ : Stacks T A := { S with R := (Function.update (Function.update S.R src (word ++ tail))
    savedPrefix (pre.reverse ++ S.R savedPrefix)) }
  obtain ⟨v₂, hu₂, he₂⟩ := copyPrefix_exec (body := body)
    (show [width, src, dst, savedWord, tmp].Nodup by simp_all) v₁ S₁ word tail
    (by simp [S₁, ‹src ≠ savedPrefix›])
    (by simpa [S₁, ‹width ≠ src›, ‹width ≠ savedPrefix›] using hwidth)
    (by simp [S₁, ‹src ≠ savedWord›.symm, ‹savedPrefix ≠ savedWord›.symm, hword])
    (by simp [S₁, ‹src ≠ tmp›.symm, ‹savedPrefix ≠ tmp›.symm, htmp])
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R dst (word ++ S₁.R dst) }
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body savedPrefix src ‹src ≠ savedPrefix›.symm id v₂ S₂
  refine ⟨v₃, hu₃.trans (hu₂.trans hu₁), (Exec.seq he₁ (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · simp [S₂, S₁, ‹dst ≠ savedPrefix›.symm, hpre]
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    clear he₁ he₂ he₃ hu₁ hu₂ hu₃
    funext k
    simp only [S₂, S₁, movedR, Function.update_apply, List.map_id, hpre, List.append_nil]
    split_ifs <;> subst_vars <;> simp_all

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
