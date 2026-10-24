module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingResizeStep
public import IntegerMultBounds.MathlibTM2.Routing.MatchingCoordinateLoop

/-! A fixed loop converts arbitrary matching tables, accumulating resized entries
and a complete source archive. Numeric widths are read from tapes, not code. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def matchingResizeLoopBody (rg : Fin 14 → Fin T) : Pr P T Q A U :=
  .seq (matchingResizeStepProgram rg) (.act (peekR (rg 10)))

def matchingResizeTraceBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 14 → Fin T)
    (L W : ℕ) : List (ℕ × ℕ) → Fin T → List (Fin (A + 4))
  | [] => R
  | x :: xs => matchingResizeTraceBank
      (matchingResizeStepBank R rg L W x.1 x.2 (matchingEntryWords L xs)) rg L W xs

theorem matchingResizeTraceBank_eq
    (R : Fin T → List (Fin (A + 4))) (rg : Fin 14 → Fin T) (hrg : Function.Injective rg)
    (L W : ℕ) (xs : List (ℕ × ℕ)) (hinput : R (rg 10) = matchingEntryWords L xs) :
    matchingResizeTraceBank R rg L W xs =
      Function.update (Function.update (Function.update R (rg 10) [])
        (rg 11) ((matchingEntryWords L xs).reverse ++ R (rg 11)))
        (rg 13) ((matchingEntryWords W xs).reverse ++ R (rg 13)) := by
  induction xs generalizing R with
  | nil =>
    funext j
    by_cases h10 : j = rg 10 <;> by_cases h11 : j = rg 11 <;> by_cases h13 : j = rg 13 <;>
      simp [matchingResizeTraceBank, matchingEntryWords, h10, h11, h13, hrg.eq_iff, hinput]
  | cons x xs ih =>
    rw [matchingResizeTraceBank, ih _ (by simp [matchingResizeStepBank, hrg.eq_iff])]
    funext j
    by_cases h10 : j = rg 10
    · subst j; simp [matchingResizeStepBank, hrg.eq_iff]
    by_cases h11 : j = rg 11
    · subst j; simp [matchingResizeStepBank, matchingEntryWords, hrg.eq_iff, List.append_assoc]
    by_cases h13 : j = rg 13
    · subst j; simp [matchingResizeStepBank, matchingEntryWords, hrg.eq_iff, List.append_assoc]
    · simp [matchingResizeStepBank, h10, h11, h13]

theorem matchingResizeLoop_exec (body : P → Pr P T Q A U)
    (rg : Fin 14 → Fin T) (hrg : Function.Injective rg) (M L W : ℕ) (hW : W < 2 ^ M)
    (xs : List (ℕ × ℕ)) (hfit : ∀ x ∈ xs, x.1 < 2 ^ L ∧ x.2 < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg 0) = binSyms M W) (hinput : S.R (rg 10) = matchingEntryWords L xs)
    (hblank : ∀ j : Fin 14, j ≠ 0 → j ≠ 10 → j ≠ 11 → j ≠ 13 → S.R (rg j) = [])
    (hflag : v.flag = xs.head?.isSome) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ xs.length * (4 * M * (4 * W + 11) + 36 * L + 56 * W + 110) + 1 ∧
      Exec body (.loop (·.flag) (matchingResizeLoopBody rg)) (mk v S) m
        (mk v' { S with R := matchingResizeTraceBank S.R rg L W xs }) := by
  induction xs generalizing v S with
  | nil =>
    exact ⟨v, 1, rfl, by simp, Exec.loop_false
      (by simpa only [List.head?_nil, Option.isSome_none, mk_var] using hflag)⟩
  | cons x xs ih =>
    obtain ⟨v₁, m₁, hu₁, hm₁, hex₁⟩ := matchingResizeStep_exec body rg hrg M L W x.1 x.2 hW
      (hfit x (by simp)).1 (hfit x (by simp)).2 (matchingEntryWords L xs) v S hwidth
      (by simpa only [matchingEntryWords] using hinput) hblank
    let C : Stacks T A := { S with R := matchingResizeStepBank S.R rg L W x.1 x.2 (matchingEntryWords L xs) }
    have hc : C.R (rg 10) = matchingEntryWords L xs := by simp [C, matchingResizeStepBank, hrg.eq_iff]
    have keep (j : Fin 14) (h10 : j ≠ 10) (h11 : j ≠ 11) (h13 : j ≠ 13) : C.R (rg j) = S.R (rg j) := by
      simp [C, matchingResizeStepBank, hrg.eq_iff, h10, h11, h13]
    let u := { v₁ with flag := xs.head?.isSome }
    have hp : (peekR (rg 10) : Act T Q A U).run (mk v₁ C) = mk u C := by
      simp only [peekR_run, hc, matchingEntryWords_head]; rfl
    obtain ⟨v₂, m₂, hu₂, hm₂, hex₂⟩ := ih (fun y hy => hfit y (by simp [hy])) u C
      ((keep 0 (by decide) (by decide) (by decide)).trans hwidth) hc
      (fun j h0 h10 h11 h13 => (keep j h10 h11 h13).trans (hblank j h0 h10 h11 h13)) rfl
    refine ⟨v₂, (m₁ + 1) + m₂ + 1, hu₂.trans hu₁, ?_, ?_⟩
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    · exact Exec.cast (Exec.loop_true
        (by simpa only [List.head?_cons, Option.isSome_some, mk_var] using hflag)
        (Exec.seq hex₁ (hp ▸ Exec.act (body := body) _ (mk v₁ C))) hex₂) (by omega) rfl

end IntegerMultBounds.MathlibTM2.Routing
