module

public import IntegerMultBounds.MathlibTM2.Routing.DelimitedBankLoad
public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! Encode a fixed register bank into the metadata format consumed by its
loader. Code depends on the register list, never on the words being copied. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def delimitedBankCopy (dst tmp work : Fin T) (delimiter : Fin (A + 4)) : List (Fin T) → Pr P T Q A U
  | [] => .act .done
  | src :: sources => .seq (delimitedBankCopy dst tmp work delimiter sources)
      (.seq (.act (Action.push (.rt dst) (fun _ => delimiter) .done)) (bcopy src dst tmp work))

def delimitedBankCopyCost : List (Fin T × List (Fin (A + 4))) → ℕ
  | [] => 1
  | (_, word) :: jobs => delimitedBankCopyCost jobs + (1 + (6 * word.length + 6))

/-- Copy every source without changing it, preserving arbitrary destination
suffix and restoring both scratch registers. Repeated source registers are allowed. -/
theorem delimitedBankCopy_exec (body : P → Pr P T Q A U)
    (dst tmp work : Fin T) (hreg : [dst, tmp, work].Nodup) (delimiter : Fin (A + 4))
    (jobs : List (Fin T × List (Fin (A + 4))))
    (hseparate : ∀ j ∈ jobs, j.1 ≠ dst ∧ j.1 ≠ tmp ∧ j.1 ≠ work)
    (v : HS T Q A U) (S : Stacks T A)
    (hwords : ∀ j ∈ jobs, S.R j.1 = j.2) (htmp : S.R tmp = []) (hwork : S.R work = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (delimitedBankCopy dst tmp work delimiter (jobs.map Prod.fst)) (mk v S)
        (delimitedBankCopyCost jobs)
        (mk v' { S with R := Function.update S.R dst (delimitedBankFrames delimiter jobs ++ S.R dst) }) := by
  have hregs := hreg
  regs_ne hregs
  induction jobs generalizing v S with
  | nil =>
      refine ⟨v, rfl, ?_⟩
      simpa [delimitedBankCopy, delimitedBankCopyCost, delimitedBankFrames] using
        (Exec.act (body := body) (.done : Act T Q A U) (mk v S))
  | cons j jobs ih =>
      obtain ⟨hjd, hjt, hjw⟩ := hseparate j (by simp)
      obtain ⟨v₁, hu₁, he₁⟩ := ih (fun k hk => hseparate k (by simp [hk])) v S
        (fun k hk => hwords k (by simp [hk])) htmp hwork
      let C : Stacks T A :=
        { S with R := Function.update S.R dst (delimitedBankFrames delimiter jobs ++ S.R dst) }
      let D : Stacks T A := { C with R := Function.update C.R dst (delimiter :: C.R dst) }
      have hp : (Action.push (.rt dst) (fun _ => delimiter) .done : Act T Q A U).run (mk v₁ C) =
          mk v₁ D := by simp [Action.run, update_rt, D]
      obtain ⟨v₂, hu₂, he₂⟩ := bcopy_exec (body := body) (a := j.1) (c := dst) (t₁ := tmp) (t₂ := work)
        (by simp_all) v₁ D (by simp [D, C, ‹dst ≠ tmp›.symm, htmp])
        (by simp [D, C, ‹dst ≠ work›.symm, hwork])
      have hj : D.R j.1 = j.2 := by
        simpa [D, C, hjd] using hwords j (by simp)
      have hfinal : ({ D with R := Function.update D.R dst (j.2 ++ D.R dst) } : Stacks T A) =
          { S with R := (Function.update S.R dst
            (delimitedBankFrames delimiter (j :: jobs) ++ S.R dst)) } := by
        simp [D, C, delimitedBankFrames, List.append_assoc]
      rw [hj, hfinal] at he₂
      exact ⟨v₂, hu₂.trans hu₁, Exec.seq he₁ (Exec.seq (hp ▸ Exec.act (body := body) _ (mk v₁ C)) he₂)⟩

/-- Six steps per copied symbol, seven per register, and one terminal step. -/
theorem delimitedBankCopyCost_eq (delimiter : Fin (A + 4))
    (jobs : List (Fin T × List (Fin (A + 4)))) :
    delimitedBankCopyCost jobs = 6 * (delimitedBankFrames delimiter jobs).length + jobs.length + 1 := by
  induction jobs with
  | nil => rfl
  | cons j jobs ih =>
      simp only [delimitedBankCopyCost, delimitedBankFrames, List.length_append, List.length_cons, ih]
      omega

end IntegerMultBounds.MathlibTM2.Routing
