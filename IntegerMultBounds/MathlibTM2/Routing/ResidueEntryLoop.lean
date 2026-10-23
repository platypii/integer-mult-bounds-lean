module

public import IntegerMultBounds.MathlibTM2.Routing.ResidueEntryStep
public import IntegerMultBounds.MathlibTM2.Routing.MatchingCoordinateLoop

/-! Scan an arbitrary list of matching entries with one fixed shared workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def residueEntryLoopBody (rg : Fin 18 → Fin T) : Pr P T Q A U :=
  .seq (residueEntryStepProgram rg) (.act (peekR (rg 14)))

def residueEntryTraceBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 18 → Fin T)
    (L Lk k r : ℕ) : List (ℕ × ℕ) → Fin T → List (Fin (A + 4))
  | [] => R
  | x :: xs => residueEntryTraceBank
      (residueEntryStepBank R rg L Lk x.1 x.2 k r (matchingEntryWords L xs)) rg L Lk k r xs

theorem residueEntryLoop_exec (body : P → Pr P T Q A U)
    (rg : Fin 18 → Fin T) (hrg : Function.Injective rg) (L Lk k r : ℕ)
    (hk : k < 2 ^ Lk) (hk0 : 0 < k) (hr : r < 2 ^ Lk)
    (xs : List (ℕ × ℕ)) (hfit : ∀ x ∈ xs, x.1 < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A)
    (hinput : S.R (rg 14) = matchingEntryWords L xs)
    (hblank : ∀ j : Fin 18, j = 0 ∨ j = 12 ∨ j = 13 ∨ (2 ≤ j.val ∧ j.val < 10) → S.R (rg j) = [])
    (hstride : S.R (rg 1) = binSyms Lk k) (hresidue : S.R (rg 11) = binSyms Lk r)
    (htmp : S.R (rg 16) = []) (hflag : v.flag = xs.head?.isSome) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ xs.length * (residueDispatchCost L Lk + 28 * L + 47) + 1 ∧
      Exec body (.loop (·.flag) (residueEntryLoopBody rg)) (mk v S) steps
        (mk v' { S with R := residueEntryTraceBank S.R rg L Lk k r xs }) := by
  induction xs generalizing v S with
  | nil => exact ⟨v, 1, rfl, by simp, Exec.loop_false (by simpa only [List.head?_nil, Option.isSome_none, mk_var] using hflag)⟩
  | cons x xs ih =>
    obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := residueEntryStep_exec body rg hrg L Lk x.1 x.2 k r
      (hfit x (by simp)) hk hk0 hr (matchingEntryWords L xs) v S
      (by simpa only [matchingEntryWords] using hinput) hblank hstride hresidue htmp
    let G : Stacks T A := { S with R := residueEntryStepBank S.R rg L Lk x.1 x.2 k r (matchingEntryWords L xs) }
    have hc : G.R (rg 14) = matchingEntryWords L xs := by
      simp [G, residueEntryStepBank, hrg.eq_iff]
    have hkeep (j : Fin 18) (hs : j ≠ 14) (ha : j ≠ 15) (hc : j ≠ 17) : G.R (rg j) = S.R (rg j) := by
      simp [G, residueEntryStepBank, hrg.eq_iff, hs, ha, hc]
    let u := { v₁ with flag := xs.head?.isSome }
    have hp : (peekR (rg 14) : Act T Q A U).run (mk v₁ G) = mk u G := by
      simp only [peekR_run, hc, matchingEntryWords_head]; rfl
    obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := ih (fun y hy => hfit y (by simp [hy])) u G hc
      (by intro j hj
          rw [hkeep j (by intro he; subst j; simp at hj)
            (by intro he; subst j; simp at hj) (by intro he; subst j; simp at hj)]
          exact hblank j hj)
      ((hkeep 1 (by decide) (by decide) (by decide)).trans hstride)
      ((hkeep 11 (by decide) (by decide) (by decide)).trans hresidue)
      ((hkeep 16 (by decide) (by decide) (by decide)).trans htmp) rfl
    refine ⟨v₂, (m₁ + 1) + m₂ + 1, hu₂.trans hu₁, ?_, ?_⟩
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    · exact Exec.cast (Exec.loop_true
        (by simpa only [List.head?_cons, Option.isSome_some, mk_var] using hflag)
        (Exec.seq he₁ (hp ▸ Exec.act (body := body) _ (mk v₁ G))) he₂) (by omega) rfl

end IntegerMultBounds.MathlibTM2.Routing
