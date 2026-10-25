module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! # Produce a repeated operand stream with paid copying -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Copy then move through fresh workspace, preserving order inside every word. -/
def duplicateStream (src buf tmp : Fin T) : Pr P T Q A U :=
  .seq (copyR src buf tmp id) (moveR buf src id)

/-- The source becomes two consecutive copies and both work stacks return empty. -/
theorem duplicateStream_exec {src buf tmp : Fin T} (hreg : [src, buf, tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (xs : List (Fin (A + 4)))
    (hsrc : S.R src = xs) (hbuf : S.R buf = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (duplicateStream src buf tmp) (mk v S) (6 * xs.length + 6)
        (mk v' { S with R := Function.update S.R src (xs ++ xs) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := copyR_exec body src buf tmp ‹src ≠ buf› ‹src ≠ tmp› ‹buf ≠ tmp› id v S htmp
  let S₁ : Stacks T A := { S with R := Function.update S.R buf xs.reverse }
  have he₁' : Exec body (copyR src buf tmp id) (mk v S) (4 * xs.length + 4) (mk v₁ S₁) := by
    simpa only [hsrc, hbuf, List.map_id, List.append_nil] using he₁
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body buf src ‹src ≠ buf›.symm id v₁ S₁
  refine ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁' he₂).cast ?_ ?_⟩
  · simp [S₁]
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hs : k = src
    · subst k
      simp [S₁, movedR, ‹src ≠ buf›, hsrc]
    · by_cases hb : k = buf
      · subst k
        simp [S₁, movedR, ‹src ≠ buf›.symm, hbuf]
      · simp [S₁, movedR, hs, hb]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
