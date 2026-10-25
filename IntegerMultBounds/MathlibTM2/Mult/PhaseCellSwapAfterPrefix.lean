module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! Swap two equally sized borrowed blocks behind a counted prefix. Three
reversed saves are moved back once, preserving each original symbol order. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ T Q A U}

def swapAfterPrefix (skip width src savedPrefix savedX savedY tmp : Fin T) : Pr P₀ T Q A U :=
  .seq (transfer skip src savedPrefix tmp) (.seq (transfer width src savedX tmp)
    (.seq (transfer width src savedY tmp) (.seq (moveR savedX src id)
      (.seq (moveR savedY src id) (moveR savedPrefix src id)))))

theorem swapAfterPrefix_exec {skip width src savedPrefix savedX savedY tmp : Fin T}
    (hreg : [skip, width, src, savedPrefix, savedX, savedY, tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (pre xs ys tail : List (Fin (A + 4)))
    (hsrc : S.R src = pre ++ (xs ++ (ys ++ tail)))
    (hskip : (S.R skip).length = pre.length)
    (hwidthX : (S.R width).length = xs.length) (hwidthY : (S.R width).length = ys.length)
    (hfresh : ∀ k ∈ [savedPrefix, savedX, savedY, tmp], S.R k = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (swapAfterPrefix skip width src savedPrefix savedX savedY tmp) (mk v S)
        (6 * pre.length + 12 * xs.length + 18)
        (mk v' { S with R := Function.update S.R src (pre ++ (ys ++ (xs ++ tail))) }) := by
  have hreg' := hreg
  regs_ne hreg'
  have hps : savedPrefix ≠ src := ‹src ≠ savedPrefix›.symm
  have hxs : savedX ≠ src := ‹src ≠ savedX›.symm
  have hys : savedY ≠ src := ‹src ≠ savedY›.symm
  have hxp : savedX ≠ savedPrefix := ‹savedPrefix ≠ savedX›.symm
  have hyp : savedY ≠ savedPrefix := ‹savedPrefix ≠ savedY›.symm
  have hyx : savedY ≠ savedX := ‹savedX ≠ savedY›.symm
  obtain ⟨v₁, hu₁, he₁⟩ := transfer_exec (body := body)
    (show [skip, src, savedPrefix, tmp].Nodup by simp_all) v S pre (xs ++ (ys ++ tail)) hsrc hskip
    (hfresh tmp (by simp))
  let S₁ : Stacks T A := { S with R := (Function.update (Function.update S.R src (xs ++ (ys ++ tail)))
    savedPrefix (pre.reverse ++ S.R savedPrefix)) }
  obtain ⟨v₂, hu₂, he₂⟩ := transfer_exec (body := body)
    (show [width, src, savedX, tmp].Nodup by simp_all) v₁ S₁ xs (ys ++ tail)
    (by simp [S₁, ‹src ≠ savedPrefix›]) (by simpa [S₁, ‹width ≠ src›, ‹width ≠ savedPrefix›] using hwidthX)
    (by simpa [S₁, ‹src ≠ tmp›.symm, ‹savedPrefix ≠ tmp›.symm] using hfresh tmp (by simp))
  let S₂ : Stacks T A := { S₁ with R := (Function.update (Function.update S₁.R src (ys ++ tail))
    savedX (xs.reverse ++ S₁.R savedX)) }
  obtain ⟨v₃, hu₃, he₃⟩ := transfer_exec (body := body)
    (show [width, src, savedY, tmp].Nodup by simp_all) v₂ S₂ ys tail
    (by simp [S₂, ‹src ≠ savedX›]) (by simpa [S₂, S₁, ‹width ≠ src›, ‹width ≠ savedPrefix›, ‹width ≠ savedX›] using hwidthY)
    (by simpa [S₂, S₁, ‹src ≠ tmp›.symm, ‹savedPrefix ≠ tmp›.symm, ‹savedX ≠ tmp›.symm] using hfresh tmp (by simp))
  let S₃ : Stacks T A := { S₂ with R := (Function.update (Function.update S₂.R src tail)
    savedY (ys.reverse ++ S₂.R savedY)) }
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body savedX src ‹src ≠ savedX›.symm id v₃ S₃
  let S₄ : Stacks T A := { S₃ with R := movedR S₃.R savedX src id (S₃.R savedX) }
  obtain ⟨v₅, hu₅, he₅⟩ := moveR_exec body savedY src ‹src ≠ savedY›.symm id v₄ S₄
  let S₅ : Stacks T A := { S₄ with R := movedR S₄.R savedY src id (S₄.R savedY) }
  obtain ⟨v₆, hu₆, he₆⟩ := moveR_exec body savedPrefix src ‹src ≠ savedPrefix›.symm id v₅ S₅
  refine ⟨v₆, hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))),
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅ he₆))))).cast ?_ ?_⟩
  · simp [S₅, S₄, S₃, S₂, S₁, movedR, hfresh savedPrefix (by simp), hfresh savedX (by simp),
      hfresh savedY (by simp), *]
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    · clear he₁ he₂ he₃ he₄ he₅ he₆
      funext k
      by_cases hk : k = src
      · subst k
        simp [S₅, S₄, S₃, S₂, S₁, movedR, *]
      by_cases hkp : k = savedPrefix
      · subst k
        simp [S₅, S₄, S₃, S₂, S₁, movedR, *, hfresh savedPrefix (by simp)]
      by_cases hkx : k = savedX
      · subst k
        simp [S₅, S₄, S₃, S₂, S₁, movedR, *, hfresh savedX (by simp)]
      by_cases hky : k = savedY
      · subst k
        simp [S₅, S₄, S₃, S₂, S₁, movedR, *, hfresh savedY (by simp)]
      simp [S₅, S₄, S₃, S₂, S₁, movedR, Function.update_apply, hk, hkp, hkx, hky]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
