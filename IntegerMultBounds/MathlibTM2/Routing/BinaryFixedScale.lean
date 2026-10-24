module

public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! Fixed-width small scalar multiples for reservoir metadata arithmetic.
Inputs survive; every temporary word is restored to blank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def binaryDoubleCopyProgram (src dst tmp work : Fin T) : Pr P T Q A U :=
  .seq (bcopy src dst tmp work) (bshift dst tmp (fun _ => bitSymbol false))

theorem binaryDoubleCopy_exec (body : P → Pr P T Q A U)
    (src dst tmp work : Fin T) (hreg : [src, dst, tmp, work].Nodup) (L x : ℕ)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R src = binSyms L x)
    (hdst : S.R dst = []) (htmp : S.R tmp = []) (hwork : S.R work = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (binaryDoubleCopyProgram src dst tmp work) (mk v S) (10 * L + 14)
        (mk v' { S with R := Function.update S.R dst (binSyms L (2 * x)) }) := by
  have hregs := hreg
  regs_ne hregs
  obtain ⟨v₁, hu₁, he₁⟩ := bcopy_exec (body := body) hreg v S htmp hwork
  rw [hsrc, hdst, List.append_nil, length_binSyms] at he₁
  let C : Stacks T A := { S with R := Function.update S.R dst (binSyms L x) }
  obtain ⟨v₂, hu₂, he₂⟩ := bshift_exec (body := body) ‹dst ≠ tmp› (fun _ => bitSymbol false) v₁ C
    (by simpa [C, ‹dst ≠ tmp›.symm] using htmp)
  have hword : C.R dst = binSyms L x := by simp [C]
  rw [hword, length_binSyms, binSyms_shift] at he₂
  refine ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁ he₂).cast (by ring) ?_⟩
  simp [C]

end IntegerMultBounds.MathlibTM2.Routing
