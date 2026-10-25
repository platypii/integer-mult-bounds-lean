module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! # Consume a counted prefix without changing symbol order -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

def takePrefix (count src dst buf tmp : Fin T) : Pr P T Q A U :=
  .seq (transfer count src buf tmp) (moveR buf dst id)

/-- Consume the prefix, preserve its word order and restore both work stacks. -/
theorem takePrefix_exec {count src dst buf tmp : Fin T}
    (hreg : [count, src, dst, buf, tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (xs tail : List (Fin (A + 4)))
    (hsrc : S.R src = xs ++ tail) (hlen : (S.R count).length = xs.length)
    (hbuf : S.R buf = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (takePrefix count src dst buf tmp) (mk v S) (6 * xs.length + 6)
        (mk v' { S with R := (Function.update (Function.update S.R src tail) dst (xs ++ S.R dst)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := transfer_exec (body := body)
    (show [count, src, buf, tmp].Nodup by simp_all) v S xs tail hsrc hlen htmp
  let S₁ : Stacks T A := { S with R := (Function.update (Function.update S.R src tail)
    buf (xs.reverse ++ S.R buf)) }
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body buf dst ‹dst ≠ buf›.symm id v₁ S₁
  refine ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁ he₂).cast ?_ ?_⟩
  · simp [S₁, hbuf]
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    simp only [S₁, movedR, Function.update_apply, List.map_id, hbuf, List.append_nil]
    split_ifs <;> subst_vars <;> simp_all

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
