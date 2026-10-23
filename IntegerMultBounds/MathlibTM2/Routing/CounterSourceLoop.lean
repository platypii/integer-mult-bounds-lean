module

public import IntegerMultBounds.MathlibTM2.Routing.CounterSourceStep
public import IntegerMultBounds.MathlibTM2.Routing.WordRepeatStep

/-! A fixed count-tape loop emits consecutive binary selectors directly. Count symbols are archived for restoration. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def counterSourceLoopBody (rg : Fin 5 → Fin T) (count saved dst : Fin T) : Pr P T Q A U :=
  .seq (.act (wordRepeatArchive count saved))
    (.seq (counterSourceReverseStepProgram rg dst) (.act (peekR count)))

def counterSourceTraceBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 5 → Fin T) (count saved dst : Fin T)
    (L i : ℕ) : List (Fin (A + 4)) → Fin T → List (Fin (A + 4))
  | [] => R
  | x :: rest => counterSourceTraceBank
      (counterSourceReverseStepBank (Function.update (Function.update R count rest) saved (x :: R saved))
        rg dst L i) rg count saved dst L (i + 1) rest

def counterSourceIterationCost (L : ℕ) :=
  (10 * L + 14) + (2 * (L + 3) + 2) + 3

theorem counterSourceLoop_exec (body : P → Pr P T Q A U)
    (rg : Fin 5 → Fin T) (hrg : Function.Injective rg) (count saved dst : Fin T)
    (hreg : [count, saved, dst].Nodup) (hcsep : ∀ r, count ≠ rg r)
    (hssep : ∀ r, saved ≠ rg r) (hdsep : ∀ r, dst ≠ rg r)
    (L i : ℕ) (input : List (Fin (A + 4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hcount : S.R count = input) (hindex : S.R (rg 0) = binSyms L i)
    (hblank : ∀ r : Fin 5, r ≠ 0 → S.R (rg r) = [])
    (hflag : v.flag = input.head?.isSome) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ input.length * counterSourceIterationCost L + 1 ∧
      Exec body (.loop (·.flag) (counterSourceLoopBody rg count saved dst)) (mk v S) steps
        (mk v' { S with R := counterSourceTraceBank S.R rg count saved dst L i input }) := by
  have hn := hreg
  regs_ne hn
  induction input generalizing i v S with
  | nil =>
    exact ⟨v, 1, rfl, by simp, Exec.loop_false (by simpa only [List.head?_nil, Option.isSome_none, mk_var] using hflag)⟩
  | cons x rest ih =>
    let u := { v with sym := some x }
    let B : Stacks T A := { S with R := Function.update (Function.update S.R count rest) saved (x :: S.R saved) }
    have hp : (wordRepeatArchive count saved : Act T Q A U).run (mk v S) = mk u B := by
      simp [wordRepeatArchive, Action.run, update_rt, hcount, u, B, Ne.symm ‹count ≠ saved›]
    have hbkeep (r : Fin 5) : B.R (rg r) = S.R (rg r) := by
      simp [B, (hcsep r).symm, (hssep r).symm]
    obtain ⟨u₁, hu₁, hx₁⟩ := counterSourceReverseStep_exec body rg hrg dst hdsep L i u B
      ((hbkeep 0).trans hindex)
      ((hbkeep 1).trans (hblank 1 (by decide)))
      ((hbkeep 2).trans (hblank 2 (by decide)))
      ((hbkeep 3).trans (hblank 3 (by decide)))
    let m₁ := (10 * L + 14) + (2 * (L + 3) + 2)
    let B₁ : Stacks T A := { B with R := counterSourceReverseStepBank B.R rg dst L i }
    have hc : B₁.R count = rest := by
      simp [B₁, B, counterSourceReverseStepBank, ‹count ≠ dst›, hcsep, ‹count ≠ saved›]
    let u₂ := { u₁ with flag := rest.head?.isSome }
    have hpeek : (peekR count : Act T Q A U).run (mk u₁ B₁) = mk u₂ B₁ := by
      simp only [peekR_run, hc]; rfl
    have hnext (r : Fin 5) (hr : r ≠ 0) : B₁.R (rg r) = S.R (rg r) := by
      simp [B₁, counterSourceReverseStepBank, hrg.eq_iff, hr, (hdsep r).symm, hbkeep]
    obtain ⟨v', m₂, hu₂, hm₂, hx₂⟩ := ih (i + 1)
      u₂ B₁ hc (by simp [B₁, counterSourceReverseStepBank])
      (fun r h0 => (hnext r h0).trans (hblank r h0)) rfl
    refine ⟨v', (1 + (m₁ + 1)) + m₂ + 1, hu₂.trans (hu₁.trans rfl), ?_, ?_⟩
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      unfold counterSourceIterationCost at *
      dsimp only [m₁]
      omega
    · exact Exec.cast (Exec.loop_true (by simpa only [List.head?_cons, Option.isSome_some, mk_var] using hflag)
        (Exec.seq (hp ▸ Exec.act (body := body) _ (mk v S))
          (Exec.seq hx₁ (hpeek ▸ Exec.act (body := body) _ (mk u₁ B₁)))) hx₂) (by omega) rfl

end IntegerMultBounds.MathlibTM2.Routing
