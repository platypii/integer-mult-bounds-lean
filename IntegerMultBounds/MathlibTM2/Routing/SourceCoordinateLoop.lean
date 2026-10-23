module

public import IntegerMultBounds.MathlibTM2.Routing.SourceCoordinateWords

/-! A fixed loop compiles arbitrary coordinate/activity input streams. The
shared decoder bank is restored after every record; costs sum over the stream. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def sourceCoordinateLoopBody (rg : Fin 21 → Fin T) (src saved tmp accum : Fin T) : Pr P T Q A U :=
  .seq (sourceCoordinateReverseProgram rg src saved tmp accum) (.act (peekR src))

def sourceCoordinateTraceBank (R : Fin T → List (Fin (A + 4))) (src saved accum : Fin T)
    (Li Lk low high k : ℕ) : List (ℕ × Bool) → Fin T → List (Fin (A + 4))
  | [] => R
  | x :: xs => sourceCoordinateTraceBank
      (sourceCoordinateReverseBank R src saved accum Li Lk x.1 low high k x.2
        (sourceCoordinateInputWords Li Lk xs)) src saved accum Li Lk low high k xs

theorem sourceCoordinateLoop_exec (body : P → Pr P T Q A U)
    (rg : Fin 21 → Fin T) (hrg : Function.Injective rg) (src saved tmp accum : Fin T)
    (hreg : [src, saved, tmp, accum].Nodup)
    (hsrc : ∀ j, src ≠ rg j) (hsaved : ∀ j, saved ≠ rg j) (htmp : ∀ j, tmp ≠ rg j)
    (hacc : ∀ j, accum ≠ rg j)
    (Li Lk low high k : ℕ) (hlow : low < 2 ^ (Li + Lk)) (hhigh : high < 2 ^ (Li + Lk))
    (hk : k < 2 ^ Lk) (hk0 : 0 < k) (xs : List (ℕ × Bool))
    (hfit : ∀ x ∈ xs, x.1 < 2 ^ (Li + Lk))
    (v : HS T Q A U) (S : Stacks T A) (setup : SourceCoordinateSetup rg Li Lk low high k S)
    (hraw : S.R src = sourceCoordinateInputWords Li Lk xs)
    (htmpBlank : S.R tmp = []) (houtput : S.R (rg 19) = []) (hflag : v.flag = xs.head?.isSome) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ xs.length * sourceCoordinateIterationCost Li Lk + 1 ∧
      Exec body (.loop (·.flag) (sourceCoordinateLoopBody rg src saved tmp accum)) (mk v S) steps
        (mk v' { S with R := sourceCoordinateTraceBank S.R src saved accum Li Lk low high k xs }) := by
  have hn := hreg
  regs_ne hn
  induction xs generalizing v S with
  | nil => exact ⟨v, 1, rfl, by simp, Exec.loop_false (by simpa only [List.head?_nil, Option.isSome_none, mk_var] using hflag)⟩
  | cons x xs ih =>
    obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := sourceCoordinateReverse_exec body rg hrg src saved tmp accum hreg
      hsrc hsaved htmp hacc Li Lk x.1 low high k x.2 (hfit x (by simp)) hlow hhigh hk hk0
      (sourceCoordinateInputWords Li Lk xs) v S setup (by simpa [sourceCoordinateInputWords] using hraw) htmpBlank houtput
    let G : Stacks T A := { S with R := sourceCoordinateReverseBank S.R src saved accum Li Lk x.1 low high k x.2 (sourceCoordinateInputWords Li Lk xs) }
    have hc : G.R src = sourceCoordinateInputWords Li Lk xs := by
      simp [G, sourceCoordinateReverseBank, ‹src ≠ accum›, ‹src ≠ saved›]
    have hkeep (j : Fin T) (hs : j ≠ src) (ha : j ≠ saved) (hc : j ≠ accum) : G.R j = S.R j := by
      simp [G, sourceCoordinateReverseBank, hs, ha, hc]
    have hrkeep (j : Fin 21) : G.R (rg j) = S.R (rg j) :=
      hkeep _ (hsrc j).symm (hsaved j).symm (hacc j).symm
    have hsetup : SourceCoordinateSetup rg Li Lk low high k G := by
      refine ⟨(hrkeep 1).trans setup.low, (hrkeep 2).trans setup.high,
        (hrkeep 3).trans setup.stride, (hrkeep 4).trans setup.zero, ?_, ?_⟩
      · simpa only [hrkeep 5] using setup.width
      · intro j hj; exact (hrkeep j).trans (setup.blank j hj)
    let u := { v₁ with flag := xs.head?.isSome }
    have hp : (peekR src : Act T Q A U).run (mk v₁ G) = mk u G := by
      simp only [peekR_run, hc, sourceCoordinateInputWords_head]; rfl
    obtain ⟨v₂, m₂, hu₂, hm₂, hx₂⟩ := ih (fun y hy => hfit y (by simp [hy])) u G hsetup hc
      ((hkeep tmp ‹src ≠ tmp›.symm ‹saved ≠ tmp›.symm ‹tmp ≠ accum›).trans htmpBlank)
      ((hrkeep 19).trans houtput) rfl
    refine ⟨v₂, (m₁ + 1) + m₂ + 1, hu₂.trans hu₁, ?_, ?_⟩
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    · exact Exec.cast (Exec.loop_true
        (by simpa only [List.head?_cons, Option.isSome_some, mk_var] using hflag)
        (Exec.seq hx₁ (hp ▸ Exec.act (body := body) _ (mk v₁ G))) hx₂) (by omega) rfl

end IntegerMultBounds.MathlibTM2.Routing
