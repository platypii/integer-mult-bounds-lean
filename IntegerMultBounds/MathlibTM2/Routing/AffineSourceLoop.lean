module

public import IntegerMultBounds.MathlibTM2.Routing.AffineSourceReverseStep
public import IntegerMultBounds.MathlibTM2.Routing.WordRepeatStep

/-! A fixed count-tape loop computes affine selectors rather than reading a
source profile. Count symbols are archived for restoration. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def affineSourceLoopBody (rg : Fin 12 → Fin T) (count saved dst : Fin T) : Pr P T Q A U :=
  .seq (.act (wordRepeatArchive count saved))
    (.seq (affineSourceReverseStepProgram rg dst) (.act (peekR count)))

def affineSourceTraceBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 12 → Fin T) (count saved dst : Fin T)
    (Li Lk i k o : ℕ) : List (Fin (A + 4)) → Fin T → List (Fin (A + 4))
  | [] => R
  | x :: rest => affineSourceTraceBank
      (affineSourceReverseStepBank (Function.update (Function.update R count rest) saved (x :: R saved))
        rg dst Li Lk i k o) rg count saved dst Li Lk (i + 1) k o rest

def affineSourceIterationCost (Li Lk : ℕ) :=
  affineSourceFrameCost Li Lk + (4 * Li + 5) + (2 * (Li + Lk + 3) + 2) + 3

theorem affineSourceLoop_exec (body : P → Pr P T Q A U)
    (rg : Fin 12 → Fin T) (hrg : Function.Injective rg) (count saved dst : Fin T)
    (hreg : [count, saved, dst].Nodup) (hcsep : ∀ r, count ≠ rg r)
    (hssep : ∀ r, saved ≠ rg r) (hdsep : ∀ r, dst ≠ rg r)
    (Li Lk i k o : ℕ) (input : List (Fin (A + 4))) (hk : k < 2 ^ Lk)
    (hi : i + input.length ≤ 2 ^ Li)
    (hfit : ∀ j < input.length, (i + j) * k + o < 2 ^ (Li + Lk))
    (v : HS T Q A U) (S : Stacks T A)
    (hcount : S.R count = input) (hindex : S.R (rg 0) = binSyms Li i)
    (hstride : S.R (rg 1) = binSyms Lk k) (hoffset : S.R (rg 2) = binSyms (Li + Lk) o)
    (hblank : ∀ r : Fin 12, r ≠ 0 → r ≠ 1 → r ≠ 2 → S.R (rg r) = [])
    (hflag : v.flag = input.head?.isSome) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ input.length * affineSourceIterationCost Li Lk + 1 ∧
      Exec body (.loop (·.flag) (affineSourceLoopBody rg count saved dst)) (mk v S) steps
        (mk v' { S with R := affineSourceTraceBank S.R rg count saved dst Li Lk i k o input }) := by
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
    have hbkeep (r : Fin 12) : B.R (rg r) = S.R (rg r) := by
      simp [B, (hcsep r).symm, (hssep r).symm]
    obtain ⟨u₁, m₁, hu₁, hm₁, hx₁⟩ := affineSourceReverseStep_exec body rg hrg dst hdsep
      Li Lk i k o (by simp only [List.length_cons] at hi; omega) hk
      (by simpa using hfit 0 (by simp)) u B
      ((hbkeep 0).trans hindex) ((hbkeep 1).trans hstride) ((hbkeep 2).trans hoffset)
      (fun r h0 h1 h2 => (hbkeep r).trans (hblank r h0 h1 h2))
    let B₁ : Stacks T A := { B with R := affineSourceReverseStepBank B.R rg dst Li Lk i k o }
    have hc : B₁.R count = rest := by
      simp [B₁, B, affineSourceReverseStepBank, ‹count ≠ dst›, hcsep, ‹count ≠ saved›]
    let u₂ := { u₁ with flag := rest.head?.isSome }
    have hpeek : (peekR count : Act T Q A U).run (mk u₁ B₁) = mk u₂ B₁ := by
      simp only [peekR_run, hc]; rfl
    have hnext (r : Fin 12) (hr : r ≠ 0) : B₁.R (rg r) = S.R (rg r) := by
      simp [B₁, affineSourceReverseStepBank, hrg.eq_iff, hr, (hdsep r).symm, hbkeep]
    obtain ⟨v', m₂, hu₂, hm₂, hx₂⟩ := ih (i + 1)
      (by simp only [List.length_cons] at hi; omega)
      (by intro j hj; simpa only [Nat.add_assoc, Nat.add_comm 1] using hfit (j + 1) (by simp; omega))
      u₂ B₁ hc (by simp [B₁, affineSourceReverseStepBank])
      ((hnext 1 (by decide)).trans hstride) ((hnext 2 (by decide)).trans hoffset)
      (fun r h0 h1 h2 => (hnext r h0).trans (hblank r h0 h1 h2)) rfl
    refine ⟨v', (1 + (m₁ + 1)) + m₂ + 1, hu₂.trans (hu₁.trans rfl), ?_, ?_⟩
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      unfold affineSourceIterationCost at *
      omega
    · exact Exec.cast (Exec.loop_true (by simpa only [List.head?_cons, Option.isSome_some, mk_var] using hflag)
        (Exec.seq (hp ▸ Exec.act (body := body) _ (mk v S))
          (Exec.seq hx₁ (hpeek ▸ Exec.act (body := body) _ (mk u₁ B₁)))) hx₂) (by omega) rfl

end IntegerMultBounds.MathlibTM2.Routing
