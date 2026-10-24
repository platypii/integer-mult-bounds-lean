module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingResizeLoop
public import IntegerMultBounds.MathlibTM2.Routing.MatchingCoordinateGenerate

/-! Re-encode a matching table using a live target width, restoring the entire
source table and workspace. Only the separate output receives the resized table. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def matchingTableResizeProgram (rg : Fin 14 → Fin T) (out : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR (rg 10)))
    (.seq (.loop (·.flag) (matchingResizeLoopBody rg))
      (.seq (moveR (rg 11) (rg 10) id) (moveR (rg 13) out id)))

def matchingResizeClosedBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 14 → Fin T)
    (L W : ℕ) (xs : List (ℕ × ℕ)) : Fin T → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update R (rg 10) [])
    (rg 11) ((matchingEntryWords L xs).reverse ++ R (rg 11)))
    (rg 13) ((matchingEntryWords W xs).reverse ++ R (rg 13))

theorem matchingTableResize_clean (R : Fin T → List (Fin (A + 4))) (rg : Fin 14 → Fin T)
    (hrg : Function.Injective rg) (out : Fin T) (hout : ∀ j, out ≠ rg j)
    (L W : ℕ) (xs : List (ℕ × ℕ))
    (hinput : R (rg 10) = matchingEntryWords L xs) (hsaved : R (rg 11) = []) (haccum : R (rg 13) = []) :
    let G := matchingResizeClosedBank R rg L W xs
    let H := movedR G (rg 11) (rg 10) id (G (rg 11))
    movedR H (rg 13) out id (H (rg 13)) = Function.update R out (matchingEntryWords W xs ++ R out) := by
  dsimp only
  funext j
  by_cases ho : j = out
  · subst j; simp [movedR, matchingResizeClosedBank, hout, hrg.eq_iff, haccum]
  by_cases h10 : j = rg 10
  · subst j; simp [movedR, matchingResizeClosedBank, hrg.eq_iff, (hout _).symm, hinput, hsaved]
  by_cases h11 : j = rg 11
  · subst j; simp [movedR, matchingResizeClosedBank, hrg.eq_iff, (hout _).symm, hsaved]
  by_cases h13 : j = rg 13
  · subst j; simp [movedR, matchingResizeClosedBank, hrg.eq_iff, (hout _).symm, haccum]
  · simp [movedR, matchingResizeClosedBank, ho, h10, h11, h13]

theorem matchingTableResize_exec (body : P → Pr P T Q A U)
    (rg : Fin 14 → Fin T) (hrg : Function.Injective rg)
    (out : Fin T) (hout : ∀ j, out ≠ rg j) (M L W : ℕ) (hW : W < 2 ^ M)
    (xs : List (ℕ × ℕ)) (hfit : ∀ x ∈ xs, x.1 < 2 ^ L ∧ x.2 < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg 0) = binSyms M W) (hinput : S.R (rg 10) = matchingEntryWords L xs)
    (hblank : ∀ j : Fin 14, j ≠ 0 → j ≠ 10 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ xs.length * (4 * M * (4 * W + 11) + 40 * L + 60 * W + 118) + 6 ∧
      Exec body (matchingTableResizeProgram rg out) (mk v S) m
        (mk v' { S with R := Function.update S.R out (matchingEntryWords W xs ++ S.R out) }) := by
  let u := { v with flag := xs.head?.isSome }
  have hp : (peekR (rg 10) : Act T Q A U).run (mk v S) = mk u S := by
    simp only [peekR_run, hinput, matchingEntryWords_head]; rfl
  obtain ⟨v₁, m₁, hu₁, hm₁, hex₁⟩ := matchingResizeLoop_exec body rg hrg M L W hW xs hfit u S
    hwidth hinput (fun j h0 h10 _ _ => hblank j h0 h10) rfl
  rw [matchingResizeTraceBank_eq S.R rg hrg L W xs hinput] at hex₁
  let G : Stacks T A := { S with R := matchingResizeClosedBank S.R rg L W xs }
  obtain ⟨v₂, hu₂, hex₂⟩ := moveR_exec body (rg 11) (rg 10) (hrg.ne (by decide)) id v₁ G
  let H : Stacks T A := { G with R := movedR G.R (rg 11) (rg 10) id (G.R (rg 11)) }
  obtain ⟨v₃, hu₃, hex₃⟩ := moveR_exec body (rg 13) out (hout _).symm id v₂ H
  have hsaved := hblank 11 (by decide) (by decide)
  have haccum := hblank 13 (by decide) (by decide)
  have hs : (G.R (rg 11)).length = xs.length * (2 * L + 2) := by
    simp [G, matchingResizeClosedBank, hrg.eq_iff, hsaved, matchingEntryWords_length]
  have ha : (H.R (rg 13)).length = xs.length * (2 * W + 2) := by
    simp [H, movedR, G, matchingResizeClosedBank, hrg.eq_iff, haccum, matchingEntryWords_length]
  have hf : movedR H.R (rg 13) out id (H.R (rg 13)) =
      Function.update S.R out (matchingEntryWords W xs ++ S.R out) :=
    matchingTableResize_clean S.R rg hrg out hout L W xs hinput hsaved haccum
  rw [hs] at hex₂
  rw [ha, hf] at hex₃
  refine ⟨v₃, 1 + (m₁ + ((2 * (xs.length * (2 * L + 2)) + 2) +
    (2 * (xs.length * (2 * W + 2)) + 2))), hu₃.trans (hu₂.trans hu₁), ?_,
    Exec.seq (hp ▸ Exec.act (body := body) _ (mk v S)) (Exec.seq hex₁ (Exec.seq hex₂ hex₃))⟩
  nlinarith only [hm₁]

end IntegerMultBounds.MathlibTM2.Routing
