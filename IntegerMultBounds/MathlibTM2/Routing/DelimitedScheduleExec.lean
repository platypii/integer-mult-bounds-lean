module

public import IntegerMultBounds.MathlibTM2.Routing.DelimitedScheduleTrace

/-! Execute a fixed framed-call loop and rewind its complete metadata input.
Only the routed stream changes; all per-call and final rewind costs are charged. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U I : Type}

def delimitedScheduleProgram (src saved : Fin T) (call : Pr P T Q A U) : Pr P T Q A U :=
  .seq (.act (peekR src))
    (.seq (.loop (·.flag) (delimitedCallLoopBody src call)) (moveR saved src id))

theorem delimitedSchedule_exec (body : P → Pr P T Q A U)
    (src saved str : Fin T) (hreg : [src, saved, str].Nodup)
    (frame : I → List (Fin (A + 4)))
    (effect : I → List (Fin (A + 4)) → List (Fin (A + 4))) (price : I → ℝ)
    (Ready : Stacks T A → Prop) (call : Pr P T Q A U) (stages : List I)
    (hnonempty : ∀ i ∈ stages, frame i ≠ [])
    (hstep : ∀ i ∈ stages, ∀ (rest : List (Fin (A + 4))) (u : HS T Q A U) (B : Stacks T A),
      Ready B → B.R src = frame i ++ rest →
      let C : Stacks T A := { B with R := delimitedCallAdvanced B.R src saved str (frame i) rest (effect i (B.R str)) }
      ∃ (u' : HS T Q A U) (m : ℕ), u'.user = u.user ∧ (m : ℝ) ≤ price i ∧ Ready C ∧
        Exec body call (mk u B) m (mk u' C))
    (v : HS T Q A U) (S : Stacks T A) (hready : Ready S)
    (hsrc : S.R src = delimitedScheduleInput frame stages) (hsaved : S.R saved = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ delimitedSchedulePrice price stages +
        (2 * (delimitedScheduleInput frame stages).length + 3 : ℕ) ∧
      Exec body (delimitedScheduleProgram src saved call) (mk v S) steps
        (mk v' { S with R := Function.update S.R str (delimitedScheduleEffect effect stages (S.R str)) }) := by
  have hn := hreg
  regs_ne hn
  let u := { v with flag := (S.R src).head?.isSome }
  have hp : (peekR src : Act T Q A U).run (mk v S) = mk u S := peekR_run src v S
  obtain ⟨v₁, m₁, hu₁, hm₁, _, hx₁⟩ := delimitedCallLoop_exec body src saved str
    ‹src ≠ saved› ‹src ≠ str› frame effect price Ready call stages hnonempty hstep u S hready hsrc rfl
  let C : Stacks T A := { S with R := delimitedScheduleBank src saved str frame effect stages S.R }
  have ha : C.R saved = (delimitedScheduleInput frame stages).reverse := by
    dsimp only [C]
    rw [delimitedScheduleBank_archive src saved str ‹saved ≠ str›, hsaved, List.append_nil]
  have hc : C.R src = [] :=
    delimitedScheduleBank_src src saved str ‹src ≠ saved› ‹src ≠ str› frame effect stages S.R hsrc
  have ho : C.R str = delimitedScheduleEffect effect stages (S.R str) :=
    delimitedScheduleBank_stream src saved str frame effect stages S.R
  obtain ⟨v₂, hu₂, hx₂⟩ := moveR_exec body saved src ‹src ≠ saved›.symm id v₁ C
  have hf : movedR C.R saved src id (C.R saved) =
      Function.update S.R str (delimitedScheduleEffect effect stages (S.R str)) := by
    funext j
    by_cases hs : j = src
    · subst j
      simp [movedR, ha, hc, hsrc, ‹src ≠ str›]
    · by_cases ha' : j = saved
      · subst j
        simp [movedR, hs, hsaved, ‹saved ≠ str›]
      · by_cases ht : j = str
        · subst j
          simp [movedR, hs, ha', ho]
        · simp only [movedR, Function.update_of_ne hs, Function.update_of_ne ha',
            Function.update_of_ne ht]
          exact delimitedScheduleBank_keep src saved str j frame effect stages hs ha' ht S.R
  rw [hf, ha, List.length_reverse] at hx₂
  refine ⟨v₂, 1 + (m₁ + (2 * (delimitedScheduleInput frame stages).length + 2)),
    hu₂.trans hu₁, ?_, Exec.seq (hp ▸ Exec.act (body := body) (peekR src) (mk v S)) (Exec.seq hx₁ hx₂)⟩
  push_cast
  linarith

end IntegerMultBounds.MathlibTM2.Routing
