module

public import IntegerMultBounds.MathlibTM2.Routing.ResidueEntryTrace
public import IntegerMultBounds.MathlibTM2.Routing.MatchingCoordinateGenerate

/-! Gather residue-selected entries from a common matching table, with
complete input rewind and workspace restoration. Only the output tape changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def residueEntryGenerateProgram (rg : Fin 18 → Fin T) (out : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR (rg 14)))
    (.seq (.loop (·.flag) (residueEntryLoopBody rg))
      (.seq (moveR (rg 15) (rg 14) id) (moveR (rg 17) out id)))

theorem residueEntryOutput_length_le (L k r : ℕ) (xs : List (ℕ × ℕ)) :
    (residueEntryOutput (A := A) L k r xs).length ≤ xs.length * (2 * L + 2) := by
  rw [residueEntryOutput, matchingEntryWords_length]
  exact Nat.mul_le_mul_right _ (List.length_filter_le _ _)

theorem residueEntryGenerate_clean (R : Fin T → List (Fin (A + 4))) (rg : Fin 18 → Fin T)
    (hrg : Function.Injective rg) (out : Fin T) (hout : ∀ j, out ≠ rg j)
    (L Lk k r : ℕ) (xs : List (ℕ × ℕ))
    (hinput : R (rg 14) = matchingEntryWords L xs) (hsaved : R (rg 15) = []) (haccum : R (rg 17) = []) :
    let G := residueEntryClosedBank R rg L Lk k r xs
    let H := movedR G (rg 15) (rg 14) id (G (rg 15))
    movedR H (rg 17) out id (H (rg 17)) = Function.update R out (residueEntryOutput L k r xs ++ R out) := by
  dsimp only
  funext j
  by_cases ho : j = out
  · subst j
    simp [movedR, residueEntryClosedBank, hout, hrg.eq_iff, haccum]
  by_cases h7 : j = rg 14
  · subst j
    simp [movedR, residueEntryClosedBank, hrg.eq_iff, (hout _).symm, hinput, hsaved]
  by_cases h8 : j = rg 15
  · subst j
    simp [movedR, residueEntryClosedBank, hrg.eq_iff, (hout _).symm, hsaved]
  by_cases h10 : j = rg 17
  · subst j
    simp [movedR, residueEntryClosedBank, hrg.eq_iff, (hout _).symm, haccum]
  · simp [movedR, residueEntryClosedBank, ho, h7, h8, h10]

theorem residueEntryGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 18 → Fin T) (hrg : Function.Injective rg)
    (out : Fin T) (hout : ∀ j, out ≠ rg j) (L Lk k r : ℕ)
    (hk : k < 2 ^ Lk) (hk0 : 0 < k) (hr : r < 2 ^ Lk)
    (xs : List (ℕ × ℕ)) (hfit : ∀ x ∈ xs, x.1 < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A)
    (hinput : S.R (rg 14) = matchingEntryWords L xs)
    (hblank : ∀ j : Fin 18, j = 0 ∨ j = 12 ∨ j = 13 ∨ (2 ≤ j.val ∧ j.val < 10) → S.R (rg j) = [])
    (hstride : S.R (rg 1) = binSyms Lk k) (hresidue : S.R (rg 11) = binSyms Lk r)
    (htmp : S.R (rg 16) = []) (hsaved : S.R (rg 15) = []) (haccum : S.R (rg 17) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ xs.length * (residueDispatchCost L Lk + 28 * L + 47) +
        2 * (xs.length * (2 * L + 2)) + 2 * (xs.length * (2 * L + 2)) + 6 ∧
      Exec body (residueEntryGenerateProgram rg out) (mk v S) steps
        (mk v' { S with R := Function.update S.R out (residueEntryOutput L k r xs ++ S.R out) }) := by
  let u := { v with flag := xs.head?.isSome }
  have hp : (peekR (rg 14) : Act T Q A U).run (mk v S) = mk u S := by
    simp only [peekR_run, hinput, matchingEntryWords_head]; rfl
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := residueEntryLoop_exec body rg hrg L Lk k r hk hk0 hr xs hfit
    u S hinput hblank hstride hresidue htmp rfl
  rw [residueEntryTrace_closed S.R rg hrg L Lk k r xs hinput] at he₁
  let G : Stacks T A := { S with R := residueEntryClosedBank S.R rg L Lk k r xs }
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body (rg 15) (rg 14) (hrg.ne (by decide)) id v₁ G
  let H : Stacks T A := { G with R := movedR G.R (rg 15) (rg 14) id (G.R (rg 15)) }
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body (rg 17) out (hout _).symm id v₂ H
  have hs : (G.R (rg 15)).length = xs.length * (2 * L + 2) := by
    simp [G, residueEntryClosedBank, hrg.eq_iff, hsaved, matchingEntryWords_length]
  have ha : (H.R (rg 17)).length = (residueEntryOutput (A := A) L k r xs).length := by
    simp [H, movedR, G, residueEntryClosedBank, hrg.eq_iff, haccum]
  have hbound := residueEntryOutput_length_le (A := A) L k r xs

  have hf : movedR H.R (rg 17) out id (H.R (rg 17)) =
      Function.update S.R out (residueEntryOutput L k r xs ++ S.R out) :=
    residueEntryGenerate_clean S.R rg hrg out hout L Lk k r xs hinput hsaved haccum
  rw [hs] at he₂
  rw [ha, hf] at he₃
  exact ⟨v₃, 1 + (m₁ + ((2 * (xs.length * (2 * L + 2)) + 2) +
    (2 * (residueEntryOutput (A := A) L k r xs).length + 2))), hu₃.trans (hu₂.trans hu₁), by omega,
    Exec.seq (hp ▸ Exec.act (body := body) _ (mk v S)) (Exec.seq he₁ (Exec.seq he₂ he₃))⟩

end IntegerMultBounds.MathlibTM2.Routing
