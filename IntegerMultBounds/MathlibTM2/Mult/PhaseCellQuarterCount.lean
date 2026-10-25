module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHalfCount

/-! # Recover normalization while leaving room for amplified stage accuracy

A working precision of 4*b permits stage precision above b, as required by the
interior error's 2^b magnitude factor. Both half-count passes restore their
source symbols, and the intermediate owned header is released.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def quarterCount (count saved half dst : Fin T) : Pr P T Q A U :=
  .seq (halfCount count saved half) (.seq (halfCount half saved dst) (uclear half))

theorem quarterCount_exec {count saved half dst : Fin T}
    (hreg : [count, saved, half, dst].Nodup) (b : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hq : (S.R count).length = 4 * b) (hsaved : S.R saved = []) (hhalf : S.R half = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (quarterCount count saved half dst) (mk v S) (22 * b + 10)
        (mk v' { S with R := Function.update S.R dst (List.replicate b tick ++ S.R dst) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := halfCount_exec (body := body)
    (show [count, saved, half].Nodup by simp_all) (2 * b) v S (by omega) hsaved
  let S₁ : Stacks T A := { S with R := Function.update S.R half (List.replicate (2 * b) tick) }
  have he₁' : Exec body (halfCount count saved half) (mk v S) (6 * (2 * b) + 4) (mk v₁ S₁) := by
    simpa only [hhalf, List.append_nil] using he₁
  obtain ⟨v₂, hu₂, he₂⟩ := halfCount_exec (body := body)
    (show [half, saved, dst].Nodup by simp_all [ne_comm]) b v₁ S₁
    (by simp [S₁]) (by simpa [S₁, ‹saved ≠ half›] using hsaved)
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R dst (List.replicate b tick ++ S₁.R dst) }
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body half v₂ S₂
  have hlen : (S₂.R half).length = 2 * b := by simp [S₂, S₁, ‹half ≠ dst›]
  refine ⟨v₃, hu₃.trans (hu₂.trans hu₁), (Exec.seq he₁' (Exec.seq he₂ he₃)).cast (by rw [hlen]; omega) ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  by_cases hh : k = half
  · subst k; simp [‹half ≠ dst›, hhalf]
  · by_cases hd : k = dst
    · subst k; simp [S₂, S₁, ‹half ≠ dst›.symm]
    · simp [S₂, S₁, hh, hd]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
