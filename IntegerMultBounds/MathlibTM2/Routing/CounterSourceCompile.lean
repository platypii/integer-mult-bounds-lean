module

public import IntegerMultBounds.MathlibTM2.Routing.CounterSourceTrace

/-! Generate consecutive source selectors from a count tape and binary
index. Restore the count and reverse the accumulator into the profile output. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

theorem counterSourceWord_length (L i n : ℕ) :
    (counterSourceWord (A := A) L i n).length = n * (L + 3) := by
  induction n generalizing i with
  | zero => simp [counterSourceWord]
  | succ n ih => simp [counterSourceWord, affineProfileFrames, ih, Nat.add_mul]; omega

def counterSourceCompileProgram (rg : Fin 5 → Fin T) (count saved accum dst : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR count))
    (.seq (.loop (·.flag) (counterSourceLoopBody rg count saved accum))
      (.seq (moveR saved count id) (moveR accum dst id)))

theorem counterSourceCompile_exec (body : P → Pr P T Q A U)
    (rg : Fin 5 → Fin T) (hrg : Function.Injective rg) (count saved accum dst : Fin T)
    (hreg : [count, saved, accum, dst].Nodup)
    (hcsep : ∀ r, count ≠ rg r) (hssep : ∀ r, saved ≠ rg r)
    (hasep : ∀ r, accum ≠ rg r) (hdsep : ∀ r, dst ≠ rg r)
    (L i : ℕ) (input : List (Fin (A + 4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hcount : S.R count = input) (hindex : S.R (rg 0) = binSyms L i)
    (hsaved : S.R saved = []) (haccum : S.R accum = [])
    (hblank : ∀ r : Fin 5, r ≠ 0 → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ input.length * counterSourceIterationCost L + 2 * input.length +
        2 * (input.length * (L + 3)) + 6 ∧
      Exec body (counterSourceCompileProgram rg count saved accum dst) (mk v S) steps
        (mk v' { S with R := Function.update (Function.update S.R dst
          (counterSourceWord L i input.length ++ S.R dst)) (rg 0) (binSyms L (i + input.length)) }) := by
  have hn := hreg
  regs_ne hn
  let u := { v with flag := input.head?.isSome }
  have hp : (peekR count : Act T Q A U).run (mk v S) = mk u S := by simp only [peekR_run, hcount]; rfl
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := counterSourceLoop_exec body rg hrg count saved accum
    (by regs_nodup) hcsep hssep hasep L i input u S hcount hindex hblank rfl
  rw [counterSourceTrace_closed S.R rg count saved accum ‹count ≠ saved› ‹count ≠ accum› ‹saved ≠ accum›
    (hcsep 0) (hssep 0) (hasep 0) L i input hcount hindex] at hx₁
  let S₁ : Stacks T A := { S with R := counterSourceClosedBank S.R rg count saved accum L i input }
  have hs : S₁.R saved = input.reverse := by
    simp [S₁, counterSourceClosedBank, (hssep 0), ‹saved ≠ accum›, hsaved]
  obtain ⟨v₂, hu₂, hx₂⟩ := moveR_exec (body := body) saved count (Ne.symm ‹count ≠ saved›) id v₁ S₁
  let S₂ : Stacks T A := { S₁ with R := movedR S₁.R saved count id (S₁.R saved) }
  have ha : S₂.R accum = (counterSourceWord L i input.length).reverse := by
    simp [S₂, movedR, S₁, counterSourceClosedBank, (hasep 0), ‹count ≠ accum›.symm, ‹saved ≠ accum›.symm, haccum]
  obtain ⟨v₃, hu₃, hx₃⟩ := moveR_exec (body := body) accum dst ‹accum ≠ dst› id v₂ S₂
  have hf : movedR S₂.R accum dst id (S₂.R accum) = Function.update (Function.update S.R dst
      (counterSourceWord L i input.length ++ S.R dst)) (rg 0) (binSyms L (i + input.length)) := by
    funext j
    by_cases hj : j = rg 0
    · subst j; simp [movedR, S₂, S₁, counterSourceClosedBank, (hasep 0).symm, (hdsep 0).symm, (hssep 0).symm, (hcsep 0).symm]
    · by_cases hd : j = dst
      · subst j; simp [movedR, S₂, S₁, counterSourceClosedBank, hasep, hssep, hdsep, ‹count ≠ accum›.symm, ‹saved ≠ accum›.symm, hsaved, haccum, ‹count ≠ dst›.symm, ‹saved ≠ dst›.symm, ‹accum ≠ dst›.symm]
      · by_cases hc : j = count
        · subst j; simp [movedR, S₂, S₁, counterSourceClosedBank, hsaved, haccum, hcount, hcsep, hssep, ‹saved ≠ accum›, ‹count ≠ accum›, ‹count ≠ dst›, ‹count ≠ saved›]
        · by_cases hsj : j = saved
          · subst j; simp [movedR, S₂, S₁, counterSourceClosedBank, hssep, hsaved, ‹saved ≠ accum›, ‹saved ≠ dst›, ‹count ≠ saved›.symm]
          · by_cases haj : j = accum
            · subst j; simp [movedR, hasep, haccum, ‹accum ≠ dst›]
            · simp [movedR, S₂, S₁, counterSourceClosedBank, Function.update_apply, hj, hd, hc, hsj, haj]
  have hslen : (S₁.R saved).length = input.length := by rw [hs, List.length_reverse]
  rw [hslen] at hx₂
  rw [hf, ha, List.length_reverse, counterSourceWord_length] at hx₃
  refine ⟨v₃, 1 + (m₁ + ((2 * input.length + 2) + (2 * (input.length * (L + 3)) + 2))),
    hu₃.trans (hu₂.trans (hu₁.trans rfl)), by omega, ?_⟩
  exact Exec.seq (hp ▸ Exec.act (body := body) _ (mk v S)) (Exec.seq hx₁ (Exec.seq hx₂ hx₃))

end IntegerMultBounds.MathlibTM2.Routing
