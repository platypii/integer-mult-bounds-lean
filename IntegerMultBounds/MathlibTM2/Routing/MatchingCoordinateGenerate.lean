module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingCoordinateTrace

/-! Produce the physical-coordinate/activity stream from matching entries, with
complete input rewind and workspace restoration. Only the output tape changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def matchingCoordinateGenerateProgram (rg : Fin 11 → Fin T) (reverse : Bool) (out : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR (rg 7)))
    (.seq (.loop (·.flag) (matchingCoordinateLoopBody rg reverse))
      (.seq (moveR (rg 8) (rg 7) id) (moveR (rg 10) out id)))

theorem matchingEntryWords_length (L : ℕ) (xs : List (ℕ × ℕ)) :
    (matchingEntryWords (A := A) L xs).length = xs.length * (2 * L + 2) := by
  induction xs with
  | nil => simp [matchingEntryWords]
  | cons x xs ih => simp [matchingEntryWords, matchingEntryWord, ih, Nat.add_mul]; omega

theorem matchingCoordinateOutput_length (reverse : Bool) (Li Lk : ℕ) (xs : List (ℕ × ℕ)) :
    (matchingCoordinateOutput (A := A) reverse Li Lk xs).length = xs.length * (Li + Lk + 3) := by
  simp [matchingCoordinateOutput, sourceCoordinateInputWords_length]

theorem matchingCoordinateGenerate_clean (R : Fin T → List (Fin (A + 4))) (rg : Fin 11 → Fin T)
    (hrg : Function.Injective rg) (reverse : Bool) (out : Fin T) (hout : ∀ j, out ≠ rg j)
    (Li Lk : ℕ) (xs : List (ℕ × ℕ))
    (hinput : R (rg 7) = matchingEntryWords (Li + Lk) xs) (hsaved : R (rg 8) = []) (haccum : R (rg 10) = []) :
    let G := matchingCoordinateClosedBank R rg reverse Li Lk xs
    let H := movedR G (rg 8) (rg 7) id (G (rg 8))
    movedR H (rg 10) out id (H (rg 10)) = Function.update R out (matchingCoordinateOutput reverse Li Lk xs ++ R out) := by
  dsimp only
  funext j
  by_cases ho : j = out
  · subst j
    simp [movedR, matchingCoordinateClosedBank, hout, hrg.eq_iff, haccum]
  by_cases h7 : j = rg 7
  · subst j
    simp [movedR, matchingCoordinateClosedBank, hrg.eq_iff, (hout _).symm, hinput, hsaved]
  by_cases h8 : j = rg 8
  · subst j
    simp [movedR, matchingCoordinateClosedBank, hrg.eq_iff, (hout _).symm, hsaved]
  by_cases h10 : j = rg 10
  · subst j
    simp [movedR, matchingCoordinateClosedBank, hrg.eq_iff, (hout _).symm, haccum]
  · simp [movedR, matchingCoordinateClosedBank, ho, h7, h8, h10]

theorem matchingCoordinateGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 11 → Fin T) (hrg : Function.Injective rg) (reverse : Bool)
    (out : Fin T) (hout : ∀ j, out ≠ rg j) (Li Lk : ℕ)
    (xs : List (ℕ × ℕ)) (hfit : ∀ x ∈ xs, x.1 < 2 ^ (Li + Lk) ∧ x.2 < 2 ^ (Li + Lk))
    (v : HS T Q A U) (S : Stacks T A)
    (hinput : S.R (rg 7) = matchingEntryWords (Li + Lk) xs)
    (hblank : ∀ j : Fin 11, j.val < 7 → j ≠ 5 → S.R (rg j) = [])
    (htmp : S.R (rg 9) = []) (hsaved : S.R (rg 8) = []) (haccum : S.R (rg 10) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ xs.length * (28 * (Li + Lk) + 44) +
        2 * (xs.length * (2 * (Li + Lk) + 2)) + 2 * (xs.length * (Li + Lk + 3)) + 6 ∧
      Exec body (matchingCoordinateGenerateProgram rg reverse out) (mk v S) steps
        (mk v' { S with R := Function.update S.R out (matchingCoordinateOutput reverse Li Lk xs ++ S.R out) }) := by
  let u := { v with flag := xs.head?.isSome }
  have hp : (peekR (rg 7) : Act T Q A U).run (mk v S) = mk u S := by
    simp only [peekR_run, hinput, matchingEntryWords_head]; rfl
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := matchingCoordinateLoop_exec body rg hrg reverse Li Lk xs hfit
    u S hinput hblank htmp rfl
  rw [matchingCoordinateTrace_closed S.R rg hrg reverse Li Lk xs hinput] at he₁
  let G : Stacks T A := { S with R := matchingCoordinateClosedBank S.R rg reverse Li Lk xs }
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body (rg 8) (rg 7) (hrg.ne (by decide)) id v₁ G
  let H : Stacks T A := { G with R := movedR G.R (rg 8) (rg 7) id (G.R (rg 8)) }
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body (rg 10) out (hout _).symm id v₂ H
  have hs : (G.R (rg 8)).length = xs.length * (2 * (Li + Lk) + 2) := by
    simp [G, matchingCoordinateClosedBank, hrg.eq_iff, hsaved, matchingEntryWords_length]
  have ha : (H.R (rg 10)).length = xs.length * (Li + Lk + 3) := by
    simp [H, movedR, G, matchingCoordinateClosedBank, hrg.eq_iff, haccum, matchingCoordinateOutput_length]
  have hf : movedR H.R (rg 10) out id (H.R (rg 10)) =
      Function.update S.R out (matchingCoordinateOutput reverse Li Lk xs ++ S.R out) :=
    matchingCoordinateGenerate_clean S.R rg hrg reverse out hout Li Lk xs hinput hsaved haccum
  rw [hs] at he₂
  rw [ha, hf] at he₃
  exact ⟨v₃, 1 + (m₁ + ((2 * (xs.length * (2 * (Li + Lk) + 2)) + 2) +
    (2 * (xs.length * (Li + Lk + 3)) + 2))), hu₃.trans (hu₂.trans hu₁), by omega,
    Exec.seq (hp ▸ Exec.act (body := body) _ (mk v S)) (Exec.seq he₁ (Exec.seq he₂ he₃))⟩

end IntegerMultBounds.MathlibTM2.Routing
