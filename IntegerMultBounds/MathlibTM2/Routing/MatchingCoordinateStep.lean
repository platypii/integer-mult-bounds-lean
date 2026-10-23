module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingCoordinateEmit

/-! Load a matching entry, derive its coordinate/activity frame, and accumulate it
in reverse. The complete entry is archived and the live endpoint bank is erased. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def matchingEntryWord (L q mate : ℕ) : List (Fin (A + 4)) :=
  binSyms L q ++ separator :: (binSyms L mate ++ [separator])

def matchingCoordinateStepProgram (rg : Fin 11 → Fin T) (reverse : Bool) : Pr P T Q A U :=
  .seq (selectorRunLoadProgram (rg 7) (rg 8) (rg 0) (rg 1) (rg 9))
    (.seq (matchingCoordinateInputProgram (fun j => rg (j.castAdd 4)) reverse)
      (.seq (bclear (rg 0)) (.seq (bclear (rg 1)) (moveR (rg 6) (rg 10) id))))

def matchingCoordinateStepBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 11 → Fin T)
    (reverse : Bool) (Li Lk q mate : ℕ) (rest : List (Fin (A + 4))) :=
  Function.update (Function.update (Function.update R (rg 7) rest)
    (rg 8) ((matchingEntryWord (Li + Lk) q mate).reverse ++ R (rg 8))) (rg 10)
    ((sourceCoordinateInputRecord Li Lk (matchingCoordinateInput reverse q mate).1
      (matchingCoordinateInput reverse q mate).2).reverse ++ R (rg 10))

theorem matchingCoordinateStep_exec (body : P → Pr P T Q A U)
    (rg : Fin 11 → Fin T) (hrg : Function.Injective rg) (reverse : Bool)
    (Li Lk q mate : ℕ) (hq : q < 2 ^ (Li + Lk)) (hmate : mate < 2 ^ (Li + Lk))
    (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hinput : S.R (rg 7) = matchingEntryWord (Li + Lk) q mate ++ rest)
    (hblank : ∀ j : Fin 11, j.val < 7 → j ≠ 5 → S.R (rg j) = [])
    (htmp : S.R (rg 9) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps + 2 ≤ 28 * (Li + Lk) + 44 ∧
      Exec body (matchingCoordinateStepProgram rg reverse) (mk v S) steps
        (mk v' { S with R := matchingCoordinateStepBank S.R rg reverse Li Lk q mate rest }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := selectorRunLoad_exec body (rg 7) (rg 8) (rg 0) (rg 1) (rg 9)
    (by simp [List.nodup_cons, hrg.eq_iff]) (Li + Lk) (Li + Lk) q mate rest v S
    (by simpa [matchingEntryWord, List.append_assoc] using hinput)
    (hblank 0 (by decide) (by decide)) (hblank 1 (by decide) (by decide)) htmp
  let B := selectorRunLoaded S.R (rg 7) (rg 8) (rg 0) (rg 1) (binSyms (Li + Lk) q) (binSyms (Li + Lk) mate) rest
  let G : Stacks T A := { S with R := B }
  have hkeep (j : Fin 11) (h0 : j ≠ 0) (h1 : j ≠ 1) (h7 : j ≠ 7) (h8 : j ≠ 8) : G.R (rg j) = S.R (rg j) := by
    simp [G, B, selectorRunLoaded, hrg.eq_iff, h0, h1, h7, h8]
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := matchingCoordinateInput_exec body (fun j => rg (j.castAdd 4))
    (by intro i j h; exact Fin.ext (congrArg (fun x : Fin 11 => x.val) (hrg h))) reverse Li Lk q mate hq hmate v₁ G
    (by simp [G, B, selectorRunLoaded, hrg.eq_iff])
    (by simp [G, B, selectorRunLoaded])
    (by intro j hj; rcases hj with rfl | rfl | rfl <;>
        simpa [G, B, selectorRunLoaded, hrg.eq_iff] using hblank _ (by decide) (by decide))
  let word := sourceCoordinateInputRecord (A := A) Li Lk (matchingCoordinateInput reverse q mate).1 (matchingCoordinateInput reverse q mate).2
  have h6 : G.R (rg 6) = [] := (hkeep 6 (by decide) (by decide) (by decide) (by decide)).trans (hblank 6 (by decide) (by decide))
  simp only [show Fin.castAdd 4 (6 : Fin 7) = (6 : Fin 11) from rfl, h6, List.append_nil] at he₂
  let H : Stacks T A := { G with R := Function.update G.R (rg 6) word }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body (rg 0) v₂ H
  let J : Stacks T A := { H with R := Function.update H.R (rg 0) [] }
  obtain ⟨v₄, hu₄, _, he₄⟩ := bclear_exec body (rg 1) v₃ J
  let E : Stacks T A := { J with R := Function.update J.R (rg 1) [] }
  obtain ⟨v₅, hu₅, he₅⟩ := moveR_exec body (rg 6) (rg 10) (hrg.ne (by decide)) id v₄ E
  have h0 : (H.R (rg 0)).length = Li + Lk := by simp [H, G, B, selectorRunLoaded, hrg.eq_iff]
  have h1 : (J.R (rg 1)).length = Li + Lk := by simp [J, H, G, B, selectorRunLoaded, hrg.eq_iff]
  have hw : E.R (rg 6) = word := by simp [E, J, H, hrg.eq_iff]
  have hf : movedR E.R (rg 6) (rg 10) id (E.R (rg 6)) = matchingCoordinateStepBank S.R rg reverse Li Lk q mate rest := by
    rw [hw]
    funext j
    by_cases h7 : j = rg 7
    · subst j; simp [movedR, E, J, H, G, B, selectorRunLoaded, matchingCoordinateStepBank, word, hrg.eq_iff]
    by_cases h8 : j = rg 8
    · subst j; simp [movedR, E, J, H, G, B, selectorRunLoaded, matchingCoordinateStepBank, matchingEntryWord, word, hrg.eq_iff]
    by_cases h0 : j = rg 0
    · subst j; simp [movedR, E, J, H, G, B, selectorRunLoaded, matchingCoordinateStepBank, word, hrg.eq_iff, hblank 0 (by decide) (by decide)]
    by_cases h1 : j = rg 1
    · subst j; simp [movedR, E, J, H, G, B, selectorRunLoaded, matchingCoordinateStepBank, word, hrg.eq_iff, hblank 1 (by decide) (by decide)]
    by_cases h6 : j = rg 6
    · subst j; simp [movedR, E, J, H, G, B, selectorRunLoaded, matchingCoordinateStepBank, word, hrg.eq_iff, hblank 6 (by decide) (by decide)]
    by_cases h10 : j = rg 10
    · subst j; simp [movedR, E, J, H, G, B, selectorRunLoaded, matchingCoordinateStepBank, word, hrg.eq_iff]
    · simp [movedR, E, J, H, G, B, selectorRunLoaded, matchingCoordinateStepBank, h7, h8, h0, h1, h6, h10]
  rw [h0] at he₃
  rw [h1] at he₄
  rw [hf, hw, sourceCoordinateInputRecord_length] at he₅
  exact ⟨v₅, (4 * (Li + Lk) + 4 * (Li + Lk) + 12) + (m₂ + ((2 * (Li + Lk) + 2) +
      ((2 * (Li + Lk) + 2) + (2 * (Li + Lk + 3) + 2)))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), by omega,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))⟩

end IntegerMultBounds.MathlibTM2.Routing
