module

public import IntegerMultBounds.MathlibTM2.Routing.SparseCursorRestore

/-! Reset a binary word to zero at its existing width, restoring all scratch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def binaryResetProgram (a zero tmp work : Fin T) : Pr P T Q A U :=
  .seq (bzero a zero tmp) (sparseCursorRestoreProgram a zero tmp work)

theorem binaryReset_exec (body : P → Pr P T Q A U)
    (a zero tmp work : Fin T) (hreg : [a, zero, tmp, work].Nodup) (L x : ℕ)
    (v : HS T Q A U) (S : Stacks T A) (ha : S.R a = binSyms L x)
    (hzero : S.R zero = []) (htmp : S.R tmp = []) (hwork : S.R work = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (binaryResetProgram a zero tmp work) (mk v S) (14 * L + 14)
        (mk v' { S with R := Function.update S.R a (binSyms L 0) }) := by
  have hregs := hreg
  regs_ne hregs
  obtain ⟨v₁, hu₁, he₁⟩ := bzero_exec (body := body) (wR := a) (c := zero) (t := tmp)
    (by simp_all) v S htmp
  rw [ha, length_binSyms, hzero, List.append_nil] at he₁
  let C : Stacks T A := { S with R := Function.update S.R zero (binSyms L 0) }
  obtain ⟨v₂, hu₂, he₂⟩ := sparseCursorRestore_exec body a zero tmp work hreg L x 0 v₁ C
    (by simpa [C, ‹a ≠ zero›] using ha) (by simp [C])
    (by simpa [C, ‹zero ≠ tmp›.symm] using htmp) (by simpa [C, ‹zero ≠ work›.symm] using hwork)
  have hfinal : ({ C with R := Function.update (Function.update C.R a (binSyms L 0)) zero [] } : Stacks T A) =
      { S with R := Function.update S.R a (binSyms L 0) } := by
    congr 1
    funext r
    by_cases hr : r = zero
    · subst r; simp [‹a ≠ zero›.symm, hzero]
    · by_cases hq : r = a <;> simp [C, hr, hq, ‹a ≠ zero›]
  rw [hfinal] at he₂
  exact ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁ he₂).cast (by omega) rfl⟩

end IntegerMultBounds.MathlibTM2.Routing
