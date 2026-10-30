module

public import IntegerMultBounds.MathlibTM2.Node.Params
public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! Remove computed dummy packets by position, without inspecting their values. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def removeDummyPrefix (src keep count tmp : Fin T) : Pr P T Q A U :=
  .seq (ucopy src count tmp) (.seq (usub keep count tmp)
    (.seq (usub count src tmp) (uclear count)))

/-- Generate the discarded length from the actual source and retained real
length. The prefix may contain arbitrary numerical results. Only the payload
changes, and the retained count keeps its original symbols. -/
theorem removeDummyPrefix_exec {src keep count tmp : Fin T}
    (hreg : [src,keep,count,tmp].Nodup)
    (dummy real : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = dummy++real) (hkeep : (S.R keep).length = real.length)
    (hcount : S.R count = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (removeDummyPrefix src keep count tmp) (mk v S)
        (10*dummy.length+8*real.length+14)
        (mk v' {S with R := Function.update S.R src real}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body := body) ‹src ≠ count› ‹src ≠ tmp›
    ‹count ≠ tmp› v S htmp
  let S₁ : Stacks T A := {S with R := (Function.update S.R count
    (List.replicate (dummy.length+real.length) tick))}
  have he₁' : Exec body (ucopy src count tmp) (mk v S)
      (4*(dummy.length+real.length)+4) (mk v₁ S₁) := by
    simpa [S₁,hsrc,hcount] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := usub_exec (body := body) ‹keep ≠ count› ‹keep ≠ tmp›
    ‹count ≠ tmp› v₁ S₁ (by simp [S₁,‹count ≠ tmp›.symm,htmp])
  let S₂ : Stacks T A := {S with R := Function.update S.R count (List.replicate dummy.length tick)}
  have he₂' : Exec body (usub keep count tmp) (mk v₁ S₁)
      (4*real.length+4) (mk v₂ S₂) := by
    simpa [S₁,S₂,‹keep ≠ count›,hkeep] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := usub_exec (body := body) ‹src ≠ count›.symm ‹count ≠ tmp›
    ‹src ≠ tmp› v₂ S₂ (by simp [S₂,‹count ≠ tmp›.symm,htmp])
  let S₃ : Stacks T A := {S₂ with R := Function.update S₂.R src real}
  have he₃' : Exec body (usub count src tmp) (mk v₂ S₂)
      (4*dummy.length+4) (mk v₃ S₃) := by
    simpa [S₂,S₃,‹src ≠ count›,hsrc] using he₃
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := body) count v₃ S₃
  refine ⟨v₄,hu₄.trans (hu₃.trans (hu₂.trans hu₁)),
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' he₄))).cast ?_ ?_⟩
  · simp [S₃,S₂,‹src ≠ count›.symm]
    ring
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases his : i = src
    · subst i; simp [S₃,S₂,‹src ≠ count›]
    by_cases hic : i = count
    · subst i; simp [S₃,S₂,‹src ≠ count›.symm,hcount]
    · simp [S₃,S₂,his,hic]

/-- Dummy erasure costs at most ten steps per padded symbol plus a constant. -/
theorem removeDummyPrefix_cost_le (D R : ℕ) : 10*D+8*R+14 ≤ 10*(D+R)+14 := by omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
