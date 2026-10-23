module

public import IntegerMultBounds.MathlibTM2.Routing.SourceActivityTrace
public import IntegerMultBounds.MathlibTM2.Routing.AffineProfileCoordinates

/-! Extract activity from canonical source records and rewind the entire input.
Only the final activity output changes; all scan and archive tapes restore. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def sourceActivityGenerateProgram (src saved index localOffset tmp accum out : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR src))
    (.seq (.loop (·.flag) (sourceActivityLoopBody src saved index localOffset tmp accum))
      (.seq (moveR saved src id) (moveR accum out id)))

theorem sourceActivityGenerate_clean (R : Fin T → List (Fin (A + 4)))
    (src saved accum out : Fin T) (hreg : [src, saved, accum, out].Nodup)
    (Li Lk : ℕ) (xs : List GatedSelectedSourceChoice)
    (hraw : R src = gatedSelectedSourceWords Li Lk xs) (hsaved : R saved = []) (haccum : R accum = []) :
    let G := sourceActivityClosedBank R src saved accum Li Lk xs
    let H := movedR G saved src id (G saved)
    movedR H accum out id (H accum) = Function.update R out (sourceActivityWord xs ++ R out) := by
  have hn := hreg
  regs_ne hn
  dsimp only
  funext j
  by_cases hs : j = src <;> by_cases ha : j = saved <;> by_cases hc : j = accum <;> by_cases ho : j = out <;>
    simp_all [movedR, sourceActivityClosedBank]
  simp_all [eq_comm]

theorem sourceActivityGenerate_exec (body : P → Pr P T Q A U)
    (src saved index localOffset tmp accum out : Fin T)
    (hreg : [src, saved, index, localOffset, tmp, accum, out].Nodup)
    (Li Lk : ℕ) (xs : List GatedSelectedSourceChoice)
    (v : HS T Q A U) (S : Stacks T A)
    (hraw : S.R src = gatedSelectedSourceWords Li Lk xs)
    (hindex : S.R index = []) (hlocal : S.R localOffset = []) (htmp : S.R tmp = [])
    (hsaved : S.R saved = []) (haccum : S.R accum = []) :
    ∃ (v' : HS T Q A U), v'.user = v.user ∧
      Exec body (sourceActivityGenerateProgram src saved index localOffset tmp accum out) (mk v S)
        (xs.length * (6 * Li + 6 * (Li + Lk) + 19) +
          2 * (xs.length * (Li + (Li + Lk) + 5)) + 2 * xs.length + 6)
        (mk v' { S with R := Function.update S.R out (sourceActivityWord xs ++ S.R out) }) := by
  have hn := hreg
  regs_ne hn
  let u := { v with flag := xs.head?.isSome }
  have hp : (peekR src : Act T Q A U).run (mk v S) = mk u S := by
    simp only [peekR_run, hraw, gatedSelectedSourceWords_head]; rfl
  obtain ⟨v₁, hu₁, hx₁⟩ := sourceActivityLoop_exec body src saved index localOffset tmp accum
    (by regs_nodup) Li Lk xs u S hraw hindex hlocal htmp rfl
  rw [sourceActivityTrace_closed S.R src saved accum ‹src ≠ saved› ‹src ≠ accum› ‹saved ≠ accum› Li Lk xs hraw] at hx₁
  let G : Stacks T A := { S with R := sourceActivityClosedBank S.R src saved accum Li Lk xs }
  obtain ⟨v₂, hu₂, hx₂⟩ := moveR_exec (body := body) saved src ‹src ≠ saved›.symm id v₁ G
  let H : Stacks T A := { G with R := movedR G.R saved src id (G.R saved) }
  obtain ⟨v₃, hu₃, hx₃⟩ := moveR_exec (body := body) accum out ‹accum ≠ out› id v₂ H
  have hs : (G.R saved).length = xs.length * (Li + (Li + Lk) + 5) := by
    simp [G, sourceActivityClosedBank, ‹saved ≠ accum›, hsaved, gatedSelectedSourceWords_length]
  have ha : (H.R accum).length = xs.length := by
    simp [H, movedR, G, sourceActivityClosedBank, ‹src ≠ accum›.symm,
      ‹saved ≠ accum›.symm, haccum, sourceActivityWord]
  have hf : movedR H.R accum out id (H.R accum) = Function.update S.R out (sourceActivityWord xs ++ S.R out) :=
    sourceActivityGenerate_clean S.R src saved accum out (by regs_nodup) Li Lk xs hraw hsaved haccum
  rw [hs] at hx₂
  rw [ha, hf] at hx₃
  exact ⟨v₃, hu₃.trans (hu₂.trans hu₁),
    Exec.cast (Exec.seq (hp ▸ Exec.act (body := body) _ (mk v S)) (Exec.seq hx₁ (Exec.seq hx₂ hx₃))) (by omega) rfl⟩

end IntegerMultBounds.MathlibTM2.Routing
