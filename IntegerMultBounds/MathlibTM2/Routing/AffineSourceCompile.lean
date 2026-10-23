module

public import IntegerMultBounds.MathlibTM2.Routing.AffineSourceTrace

/-! Generate a complete affine source profile from a count tape and live binary
operands. Restore the count and reverse the accumulator into the profile output. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

theorem affineSourceWord_length (Li Lk i k o n : ℕ) :
    (affineSourceWord (A := A) Li Lk i k o n).length = n * (Li + Lk + 3) := by
  induction n generalizing i with
  | zero => simp [affineSourceWord]
  | succ n ih => simp [affineSourceWord, affineProfileFrames, ih, Nat.add_mul]; omega

def affineSourceCompileProgram (rg : Fin 12 → Fin T) (count saved accum dst : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR count))
    (.seq (.loop (·.flag) (affineSourceLoopBody rg count saved accum))
      (.seq (moveR saved count id) (moveR accum dst id)))

theorem affineSourceCompile_exec (body : P → Pr P T Q A U)
    (rg : Fin 12 → Fin T) (hrg : Function.Injective rg) (count saved accum dst : Fin T)
    (hreg : [count, saved, accum, dst].Nodup)
    (hcsep : ∀ r, count ≠ rg r) (hssep : ∀ r, saved ≠ rg r)
    (hasep : ∀ r, accum ≠ rg r) (hdsep : ∀ r, dst ≠ rg r)
    (Li Lk i k o : ℕ) (input : List (Fin (A + 4))) (hk : k < 2 ^ Lk)
    (hi : i + input.length ≤ 2 ^ Li)
    (hfit : ∀ j < input.length, (i + j) * k + o < 2 ^ (Li + Lk))
    (v : HS T Q A U) (S : Stacks T A)
    (hcount : S.R count = input) (hindex : S.R (rg 0) = binSyms Li i)
    (hstride : S.R (rg 1) = binSyms Lk k) (hoffset : S.R (rg 2) = binSyms (Li + Lk) o)
    (hsaved : S.R saved = []) (haccum : S.R accum = [])
    (hblank : ∀ r : Fin 12, r ≠ 0 → r ≠ 1 → r ≠ 2 → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ input.length * affineSourceIterationCost Li Lk + 2 * input.length +
        2 * (input.length * (Li + Lk + 3)) + 6 ∧
      Exec body (affineSourceCompileProgram rg count saved accum dst) (mk v S) steps
        (mk v' { S with R := Function.update (Function.update S.R dst
          (affineSourceWord Li Lk i k o input.length ++ S.R dst)) (rg 0) (binSyms Li (i + input.length)) }) := by
  have hn := hreg
  regs_ne hn
  let u := { v with flag := input.head?.isSome }
  have hp : (peekR count : Act T Q A U).run (mk v S) = mk u S := by simp only [peekR_run, hcount]; rfl
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := affineSourceLoop_exec body rg hrg count saved accum
    (by regs_nodup) hcsep hssep hasep Li Lk i k o input hk hi hfit u S hcount hindex hstride hoffset hblank rfl
  rw [affineSourceTrace_closed S.R rg count saved accum ‹count ≠ saved› ‹count ≠ accum› ‹saved ≠ accum›
    (hcsep 0) (hssep 0) (hasep 0) Li Lk i k o input hcount hindex] at hx₁
  let S₁ : Stacks T A := { S with R := affineSourceClosedBank S.R rg count saved accum Li Lk i k o input }
  have hs : S₁.R saved = input.reverse := by
    simp [S₁, affineSourceClosedBank, (hssep 0), ‹saved ≠ accum›, hsaved]
  obtain ⟨v₂, hu₂, hx₂⟩ := moveR_exec (body := body) saved count (Ne.symm ‹count ≠ saved›) id v₁ S₁
  let S₂ : Stacks T A := { S₁ with R := movedR S₁.R saved count id (S₁.R saved) }
  have ha : S₂.R accum = (affineSourceWord Li Lk i k o input.length).reverse := by
    simp [S₂, movedR, S₁, affineSourceClosedBank, (hasep 0), ‹count ≠ accum›.symm, ‹saved ≠ accum›.symm, haccum]
  obtain ⟨v₃, hu₃, hx₃⟩ := moveR_exec (body := body) accum dst ‹accum ≠ dst› id v₂ S₂
  have hf : movedR S₂.R accum dst id (S₂.R accum) = Function.update (Function.update S.R dst
      (affineSourceWord Li Lk i k o input.length ++ S.R dst)) (rg 0) (binSyms Li (i + input.length)) := by
    funext j
    by_cases hj : j = rg 0
    · subst j; simp [movedR, S₂, S₁, affineSourceClosedBank, (hasep 0).symm, (hdsep 0).symm, (hssep 0).symm, (hcsep 0).symm]
    · by_cases hd : j = dst
      · subst j; simp [movedR, S₂, S₁, affineSourceClosedBank, hasep, hssep, hdsep, ‹count ≠ accum›.symm, ‹saved ≠ accum›.symm, hsaved, haccum, ‹count ≠ dst›.symm, ‹saved ≠ dst›.symm, ‹accum ≠ dst›.symm]
      · by_cases hc : j = count
        · subst j; simp [movedR, S₂, S₁, affineSourceClosedBank, hsaved, haccum, hcount, hcsep, hssep, ‹saved ≠ accum›, ‹count ≠ accum›, ‹count ≠ dst›, ‹count ≠ saved›]
        · by_cases hsj : j = saved
          · subst j; simp [movedR, S₂, S₁, affineSourceClosedBank, hssep, hsaved, ‹saved ≠ accum›, ‹saved ≠ dst›, ‹count ≠ saved›.symm]
          · by_cases haj : j = accum
            · subst j; simp [movedR, hasep, haccum, ‹accum ≠ dst›]
            · simp [movedR, S₂, S₁, affineSourceClosedBank, Function.update_apply, hj, hd, hc, hsj, haj]
  have hslen : (S₁.R saved).length = input.length := by rw [hs, List.length_reverse]
  rw [hslen] at hx₂
  rw [hf, ha, List.length_reverse, affineSourceWord_length] at hx₃
  refine ⟨v₃, 1 + (m₁ + ((2 * input.length + 2) + (2 * (input.length * (Li + Lk + 3)) + 2))),
    hu₃.trans (hu₂.trans (hu₁.trans rfl)), by omega, ?_⟩
  exact Exec.seq (hp ▸ Exec.act (body := body) _ (mk v S)) (Exec.seq hx₁ (Exec.seq hx₂ hx₃))

end IntegerMultBounds.MathlibTM2.Routing
