module

public import IntegerMultBounds.MathlibTM2.Routing.SourceCoordinateTrace

/-! Compile a complete physical-coordinate stream into canonical source records.
The entire input and workspace are restored; only the final output changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def sourceCoordinateGenerateProgram (rg : Fin 21 → Fin T) (src saved tmp accum out : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR src))
    (.seq (.loop (·.flag) (sourceCoordinateLoopBody rg src saved tmp accum))
      (.seq (moveR saved src id) (moveR accum out id)))

theorem sourceCoordinateGenerate_clean (R : Fin T → List (Fin (A + 4)))
    (src saved accum out : Fin T) (hreg : [src, saved, accum, out].Nodup)
    (Li Lk low high k : ℕ) (xs : List (ℕ × Bool))
    (hraw : R src = sourceCoordinateInputWords Li Lk xs) (hsaved : R saved = []) (haccum : R accum = []) :
    let G := sourceCoordinateClosedBank R src saved accum Li Lk low high k xs
    let H := movedR G saved src id (G saved)
    movedR H accum out id (H accum) = Function.update R out (sourceCoordinateOutputWords Li Lk low high k xs ++ R out) := by
  have hn := hreg
  regs_ne hn
  dsimp only
  funext j
  by_cases hs : j = src <;> by_cases ha : j = saved <;> by_cases hc : j = accum <;> by_cases ho : j = out <;>
    simp_all [movedR, sourceCoordinateClosedBank]
  simp_all [eq_comm]

theorem sourceCoordinateGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 21 → Fin T) (hrg : Function.Injective rg) (src saved tmp accum out : Fin T)
    (hreg : [src, saved, tmp, accum, out].Nodup)
    (hsrc : ∀ j, src ≠ rg j) (hsaved : ∀ j, saved ≠ rg j) (htmp : ∀ j, tmp ≠ rg j)
    (hacc : ∀ j, accum ≠ rg j)
    (Li Lk low high k : ℕ) (hlow : low < 2 ^ (Li + Lk)) (hhigh : high < 2 ^ (Li + Lk))
    (hk : k < 2 ^ Lk) (hk0 : 0 < k) (xs : List (ℕ × Bool))
    (hfit : ∀ x ∈ xs, x.1 < 2 ^ (Li + Lk))
    (v : HS T Q A U) (S : Stacks T A) (setup : SourceCoordinateSetup rg Li Lk low high k S)
    (hraw : S.R src = sourceCoordinateInputWords Li Lk xs)
    (htmpBlank : S.R tmp = []) (houtput : S.R (rg 19) = [])
    (hsavedBlank : S.R saved = []) (haccum : S.R accum = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ xs.length * sourceCoordinateIterationCost Li Lk +
        2 * (xs.length * (Li + Lk + 3)) + 2 * (xs.length * (Li + (Li + Lk) + 5)) + 6 ∧
      Exec body (sourceCoordinateGenerateProgram rg src saved tmp accum out) (mk v S) steps
        (mk v' { S with R := Function.update S.R out (sourceCoordinateOutputWords Li Lk low high k xs ++ S.R out) }) := by
  have hn := hreg
  regs_ne hn
  let u := { v with flag := xs.head?.isSome }
  have hp : (peekR src : Act T Q A U).run (mk v S) = mk u S := by
    simp only [peekR_run, hraw, sourceCoordinateInputWords_head]; rfl
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := sourceCoordinateLoop_exec body rg hrg src saved tmp accum
    (by regs_nodup) hsrc hsaved htmp hacc Li Lk low high k hlow hhigh hk hk0 xs hfit u S setup hraw htmpBlank houtput rfl
  rw [sourceCoordinateTrace_closed S.R src saved accum ‹src ≠ saved› ‹src ≠ accum› ‹saved ≠ accum›
    Li Lk low high k xs hraw] at hx₁
  let G : Stacks T A := { S with R := sourceCoordinateClosedBank S.R src saved accum Li Lk low high k xs }
  obtain ⟨v₂, hu₂, hx₂⟩ := moveR_exec (body := body) saved src ‹src ≠ saved›.symm id v₁ G
  let H : Stacks T A := { G with R := movedR G.R saved src id (G.R saved) }
  obtain ⟨v₃, hu₃, hx₃⟩ := moveR_exec (body := body) accum out ‹accum ≠ out› id v₂ H
  have hs : (G.R saved).length = xs.length * (Li + Lk + 3) := by
    simp [G, sourceCoordinateClosedBank, ‹saved ≠ accum›, hsavedBlank, sourceCoordinateInputWords_length]
  have ha : (H.R accum).length = xs.length * (Li + (Li + Lk) + 5) := by
    simp [H, movedR, G, sourceCoordinateClosedBank, ‹src ≠ accum›.symm,
      ‹saved ≠ accum›.symm, haccum, sourceCoordinateOutputWords_length]
  have hf : movedR H.R accum out id (H.R accum) =
      Function.update S.R out (sourceCoordinateOutputWords Li Lk low high k xs ++ S.R out) :=
    sourceCoordinateGenerate_clean S.R src saved accum out (by regs_nodup) Li Lk low high k xs hraw hsavedBlank haccum
  rw [hs] at hx₂
  rw [ha, hf] at hx₃
  exact ⟨v₃, 1 + (m₁ + ((2 * (xs.length * (Li + Lk + 3)) + 2) +
      (2 * (xs.length * (Li + (Li + Lk) + 5)) + 2))), hu₃.trans (hu₂.trans hu₁), by omega,
    Exec.seq (hp ▸ Exec.act (body := body) _ (mk v S)) (Exec.seq hx₁ (Exec.seq hx₂ hx₃))⟩

end IntegerMultBounds.MathlibTM2.Routing
