module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingProfileInputs
public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! Execute the comparison choosing a matching direction's source and activity.
The matching entry and every scratch tape are preserved. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def matchingCoordinateDispatchProgram (rg : Fin 6 → Fin T) (reverse : Bool)
    (branch : Bool → Pr P T Q A U) : Pr P T Q A U :=
  .seq (blt (rg (if reverse then 1 else 0)) (rg (if reverse then 0 else 1))
    (rg 2) (rg 3) (rg 4) (rg 5))
    (.cond (fun v => symBit (v.scan (rg 5))) (branch true) (branch false))

/-- The only per-branch premise is its own execution; the matching comparison,
branch selection and full restoration are executed here and charged explicitly. -/
theorem matchingCoordinateDispatch_exec (body : P → Pr P T Q A U)
    (rg : Fin 6 → Fin T) (hrg : Function.Injective rg) (reverse : Bool)
    (branch : Bool → Pr P T Q A U) (L q mate C : ℕ)
    (hq : q < 2 ^ L) (hmate : mate < 2 ^ L)
    (v : HS T Q A U) (S S' : Stacks T A)
    (hcoordinate : S.R (rg 0) = binSyms L q) (hmateInput : S.R (rg 1) = binSyms L mate)
    (hblank : ∀ j : Fin 6, j = 2 ∨ j = 3 ∨ j = 4 → S.R (rg j) = [])
    (hbranch : ∀ u : HS T Q A U, ∃ (u' : HS T Q A U) (steps : ℕ), u'.user = u.user ∧ steps ≤ C ∧
      Exec body (branch (matchingCoordinateEnabled reverse q mate)) (mk u S) steps (mk u' S')) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ 8 * L + 9 + C ∧
      Exec body (matchingCoordinateDispatchProgram rg reverse branch) (mk v S) steps (mk v' S') := by
  cases reverse
  · obtain ⟨v₁, hu₁, hs₁, _, he₁⟩ := blt_exec body
      (a := rg 0) (b := rg 1) (tx := rg 2) (ty := rg 3) (tz := rg 4) (cy := rg 5)
      (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide))
      hq hmate v S hcoordinate hmateInput (hblank 2 (by simp)) (hblank 3 (by simp)) (hblank 4 (by simp))
    obtain ⟨v₂, steps, hu₂, hm₂, he₂⟩ := hbranch v₁
    refine ⟨v₂, (8 * L + 8) + (steps + 1), hu₂.trans hu₁, by omega, ?_⟩
    apply Exec.seq he₁
    by_cases h : q < mate
    · simp only [matchingCoordinateEnabled, Bool.false_eq_true, ↓reduceIte, h, decide_true] at he₂
      exact Exec.cond_true (by simp [mk_var, hs₁, h]) he₂
    · simp only [matchingCoordinateEnabled, Bool.false_eq_true, ↓reduceIte, h, decide_false] at he₂
      exact Exec.cond_false (by simp [mk_var, hs₁, h]) he₂
  · obtain ⟨v₁, hu₁, hs₁, _, he₁⟩ := blt_exec body
      (a := rg 1) (b := rg 0) (tx := rg 2) (ty := rg 3) (tz := rg 4) (cy := rg 5)
      (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide))
      hmate hq v S hmateInput hcoordinate (hblank 2 (by simp)) (hblank 3 (by simp)) (hblank 4 (by simp))
    obtain ⟨v₂, steps, hu₂, hm₂, he₂⟩ := hbranch v₁
    refine ⟨v₂, (8 * L + 8) + (steps + 1), hu₂.trans hu₁, by omega, ?_⟩
    apply Exec.seq he₁
    by_cases h : mate < q
    · simp only [matchingCoordinateEnabled, ↓reduceIte, h, decide_true] at he₂
      exact Exec.cond_true (by simp [mk_var, hs₁, h]) he₂
    · simp only [matchingCoordinateEnabled, ↓reduceIte, h, decide_false] at he₂
      exact Exec.cond_false (by simp [mk_var, hs₁, h]) he₂

end IntegerMultBounds.MathlibTM2.Routing
