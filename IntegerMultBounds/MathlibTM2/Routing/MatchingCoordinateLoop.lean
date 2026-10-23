module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingCoordinateStep

/-! Scan an arbitrary list of matching entries with one fixed shared workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def matchingEntryWords (L : ℕ) : List (ℕ × ℕ) → List (Fin (A + 4))
  | [] => []
  | x :: xs => matchingEntryWord L x.1 x.2 ++ matchingEntryWords L xs

theorem matchingEntryWords_head (L : ℕ) (xs : List (ℕ × ℕ)) :
    (matchingEntryWords (A := A) L xs).head?.isSome = xs.head?.isSome := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    cases hb : (binSyms L x.1 : List (Fin (A + 4))) <;>
      simp [matchingEntryWords, matchingEntryWord, hb]

def matchingCoordinateLoopBody (rg : Fin 11 → Fin T) (reverse : Bool) : Pr P T Q A U :=
  .seq (matchingCoordinateStepProgram rg reverse) (.act (peekR (rg 7)))

def matchingCoordinateTraceBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 11 → Fin T)
    (reverse : Bool) (Li Lk : ℕ) : List (ℕ × ℕ) → Fin T → List (Fin (A + 4))
  | [] => R
  | x :: xs => matchingCoordinateTraceBank
      (matchingCoordinateStepBank R rg reverse Li Lk x.1 x.2 (matchingEntryWords (Li + Lk) xs)) rg reverse Li Lk xs

theorem matchingCoordinateLoop_exec (body : P → Pr P T Q A U)
    (rg : Fin 11 → Fin T) (hrg : Function.Injective rg) (reverse : Bool) (Li Lk : ℕ)
    (xs : List (ℕ × ℕ)) (hfit : ∀ x ∈ xs, x.1 < 2 ^ (Li + Lk) ∧ x.2 < 2 ^ (Li + Lk))
    (v : HS T Q A U) (S : Stacks T A)
    (hinput : S.R (rg 7) = matchingEntryWords (Li + Lk) xs)
    (hblank : ∀ j : Fin 11, j.val < 7 → j ≠ 5 → S.R (rg j) = [])
    (htmp : S.R (rg 9) = []) (hflag : v.flag = xs.head?.isSome) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ xs.length * (28 * (Li + Lk) + 44) + 1 ∧
      Exec body (.loop (·.flag) (matchingCoordinateLoopBody rg reverse)) (mk v S) steps
        (mk v' { S with R := matchingCoordinateTraceBank S.R rg reverse Li Lk xs }) := by
  induction xs generalizing v S with
  | nil => exact ⟨v, 1, rfl, by simp, Exec.loop_false (by simpa only [List.head?_nil, Option.isSome_none, mk_var] using hflag)⟩
  | cons x xs ih =>
    obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := matchingCoordinateStep_exec body rg hrg reverse Li Lk x.1 x.2
      (hfit x (by simp)).1 (hfit x (by simp)).2 (matchingEntryWords (Li + Lk) xs) v S
      (by simpa only [matchingEntryWords] using hinput) hblank htmp
    let G : Stacks T A := { S with R := matchingCoordinateStepBank S.R rg reverse Li Lk x.1 x.2 (matchingEntryWords (Li + Lk) xs) }
    have hc : G.R (rg 7) = matchingEntryWords (Li + Lk) xs := by
      simp [G, matchingCoordinateStepBank, hrg.eq_iff]
    have hkeep (j : Fin 11) (hs : j ≠ 7) (ha : j ≠ 8) (hc : j ≠ 10) : G.R (rg j) = S.R (rg j) := by
      simp [G, matchingCoordinateStepBank, hrg.eq_iff, hs, ha, hc]
    let u := { v₁ with flag := xs.head?.isSome }
    have hp : (peekR (rg 7) : Act T Q A U).run (mk v₁ G) = mk u G := by
      simp only [peekR_run, hc, matchingEntryWords_head]; rfl
    obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := ih (fun y hy => hfit y (by simp [hy])) u G hc
      (by intro j hj h5; rw [hkeep j (by intro he; subst j; simp at hj)
          (by intro he; subst j; simp at hj) (by intro he; subst j; simp at hj)]; exact hblank j hj h5)
      ((hkeep 9 (by decide) (by decide) (by decide)).trans htmp) rfl
    refine ⟨v₂, (m₁ + 1) + m₂ + 1, hu₂.trans hu₁, ?_, ?_⟩
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    · exact Exec.cast (Exec.loop_true
        (by simpa only [List.head?_cons, Option.isSome_some, mk_var] using hflag)
        (Exec.seq he₁ (hp ▸ Exec.act (body := body) _ (mk v₁ G))) he₂) (by omega) rfl

end IntegerMultBounds.MathlibTM2.Routing
