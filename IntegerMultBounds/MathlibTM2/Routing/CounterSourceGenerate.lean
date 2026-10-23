module

public import IntegerMultBounds.MathlibTM2.Routing.CounterSourceCompile
public import IntegerMultBounds.MathlibTM2.Routing.SparseCursorRestore

/-! Generate consecutive source profiles from count and index operands, restoring
both the complete count and original index. Only the profile output changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def counterSourceGenerateProgram (rg : Fin 5 → Fin T) (count saved accum dst savedIndex : Fin T) : Pr P T Q A U :=
  .seq (bcopy (rg 0) savedIndex (rg 2) (rg 3))
    (.seq (counterSourceCompileProgram rg count saved accum dst)
      (sparseCursorRestoreProgram (rg 0) savedIndex (rg 2) (rg 3)))

theorem counterSourceGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 5 → Fin T) (hrg : Function.Injective rg) (count saved accum dst savedIndex : Fin T)
    (hreg : [count, saved, accum, dst, savedIndex].Nodup)
    (hcsep : ∀ r, count ≠ rg r) (hssep : ∀ r, saved ≠ rg r)
    (hasep : ∀ r, accum ≠ rg r) (hdsep : ∀ r, dst ≠ rg r) (hisep : ∀ r, savedIndex ≠ rg r)
    (L i : ℕ) (input : List (Fin (A + 4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hcount : S.R count = input) (hindex : S.R (rg 0) = binSyms L i)
    (hsaved : S.R saved = []) (haccum : S.R accum = []) (hsavedIndex : S.R savedIndex = [])
    (hblank : ∀ r : Fin 5, r ≠ 0 → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ input.length * counterSourceIterationCost L + 2 * input.length +
        2 * (input.length * (L + 3)) + 16 * L + 22 ∧
      Exec body (counterSourceGenerateProgram rg count saved accum dst savedIndex) (mk v S) steps
        (mk v' { S with R := Function.update S.R dst (counterSourceWord L i input.length ++ S.R dst) }) := by
  have hn := hreg
  regs_ne hn
  have hcopy : [rg 0, savedIndex, rg 2, rg 3].Nodup := by
    simp [List.nodup_cons, hrg.eq_iff, hisep, (hisep 0).symm]
  obtain ⟨v₁, hu₁, hx₁⟩ := bcopy_exec body hcopy v S
    (hblank 2 (by decide)) (hblank 3 (by decide))
  rw [hindex, hsavedIndex, List.append_nil, length_binSyms] at hx₁
  let S₁ : Stacks T A := { S with R := Function.update S.R savedIndex (binSyms L i) }
  have hrkeep (r : Fin 5) : S₁.R (rg r) = S.R (rg r) := Function.update_of_ne (hisep r).symm _ _
  obtain ⟨v₂, m₂, hu₂, hm₂, hx₂⟩ := counterSourceCompile_exec body rg hrg count saved accum dst
    (by regs_nodup) hcsep hssep hasep hdsep L i input v₁ S₁
    (by simp [S₁, ‹count ≠ savedIndex›, hcount]) ((hrkeep 0).trans hindex)
    (by simp [S₁, ‹saved ≠ savedIndex›, hsaved]) (by simp [S₁, ‹accum ≠ savedIndex›, haccum])
    (fun r h0 => (hrkeep r).trans (hblank r h0))
  have hd : S₁.R dst = S.R dst := by simp [S₁, ‹dst ≠ savedIndex›]
  rw [hd] at hx₂
  let out := counterSourceWord (A := A) L i input.length ++ S.R dst
  let S₂ : Stacks T A := { S₁ with R := Function.update (Function.update S₁.R dst out) (rg 0) (binSyms L (i + input.length)) }
  obtain ⟨v₃, hu₃, hx₃⟩ := sparseCursorRestore_exec body (rg 0) savedIndex (rg 2) (rg 3) hcopy
    L (i + input.length) i v₂ S₂ (by simp [S₂])
    (by simp [S₂, S₁, hisep, ‹dst ≠ savedIndex›.symm])
    (by simp [S₂, S₁, hrg.eq_iff, (hdsep 2).symm, (hisep 2).symm, hblank 2 (by decide)])
    (by simp [S₂, S₁, hrg.eq_iff, (hdsep 3).symm, (hisep 3).symm, hblank 3 (by decide)])
  have hf : Function.update (Function.update S₂.R (rg 0) (binSyms L i)) savedIndex [] = Function.update S.R dst out := by
    funext j
    by_cases hj : j = savedIndex
    · subst j; simp [‹dst ≠ savedIndex›.symm, hsavedIndex]
    · by_cases hc : j = rg 0
      · subst j; simp [hj, (hdsep 0).symm, hindex]
      · simp [S₂, S₁, Function.update_apply, hj, hc]
  rw [hf] at hx₃
  exact ⟨v₃, (6 * L + 6) + (m₂ + (10 * L + 10)), hu₃.trans (hu₂.trans hu₁), by omega,
    Exec.seq hx₁ (Exec.seq hx₂ hx₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
