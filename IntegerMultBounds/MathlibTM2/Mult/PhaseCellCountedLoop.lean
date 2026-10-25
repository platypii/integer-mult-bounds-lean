module

public import IntegerMultBounds.MathlibTM2.Node.Params

/-! A structural counted loop with a relational invariant. The table's scratch
values may change between rows; only the invariant and count preservation are
needed, rather than an exact preselected register file at every iteration. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def countedLoopBody (count : Fin T) (p : Pr P T Q A U) : Pr P T Q A U :=
  .seq (.act (.pop (.rt count) (fun v _ => v) .done)) (.seq p (.act (peekR count)))

def countedLoop (count : Fin T) (p : Pr P T Q A U) : Pr P T Q A U :=
  .seq (.act (peekR count)) (.loop (·.flag) (countedLoopBody count p))

theorem countedLoop_exec (count : Fin T) (p : Pr P T Q A U) (N c : ℕ)
    (Inv : ℕ → Stacks T A → Prop)
    (hstable : ∀ j S xs, Inv j S → Inv j { S with R := Function.update S.R count xs })
    (hstep : ∀ j < N, ∀ (v : HS T Q A U) S, Inv j S →
      ∃ v' S' m, v'.user = v.user ∧ m ≤ c ∧ Exec body p (mk v S) m (mk v' S') ∧
        S'.R count = S.R count ∧ Inv (j+1) S')
    (v : HS T Q A U) (S : Stacks T A) (hcount : (S.R count).length = N) (hInv : Inv 0 S) :
    ∃ v' S' m, v'.user = v.user ∧ m ≤ N*(c+3)+2 ∧
      Exec body (countedLoop count p) (mk v S) m (mk v' S') ∧ S'.R count = [] ∧ Inv N S' := by
  have hloop : ∀ (xs : List (Fin (A+4))) (j : ℕ) (vi : HS T Q A U) Si,
      Si.R count = xs → j+xs.length ≤ N → Inv j Si → vi.flag = xs.head?.isSome →
      ∃ vf Sf m, vf.user = vi.user ∧ m ≤ xs.length*(c+3)+1 ∧
        Exec body (.loop (·.flag) (countedLoopBody count p)) (mk vi Si) m (mk vf Sf) ∧
        Sf.R count = [] ∧ Inv (j+xs.length) Sf := by
    intro xs
    induction xs with
    | nil =>
      intro j vi Si hxs _ hI hflag
      exact ⟨vi, Si, 1, rfl, by simp, Exec.loop_false (by simpa using hflag), hxs,
        by simpa using hI⟩
    | cons x xs ih =>
      intro j vi Si hxs hN hI hflag
      let S₁ : Stacks T A := { Si with R := Function.update Si.R count xs }
      have hpop : Exec body (.act (.pop (.rt count) (fun v _ => v) .done)) (mk vi Si) 1 (mk vi S₁) := by
        simpa [S₁, Action.run, hxs, update_rt] using
          (Exec.act (body := body) (.pop (.rt count) (fun v _ => v) .done) (mk vi Si))
      obtain ⟨v₁, S₂, m₁, hu₁, hm₁, he₁, hc₁, hi₁⟩ := hstep j (by simp at hN; omega) vi S₁
        (hstable j Si xs hI)
      have hc₂ : S₂.R count = xs := by simpa [S₁] using hc₁
      have hpeek := Exec.act (body := body) (peekR count) (mk v₁ S₂)
      rw [peekR_run] at hpeek
      obtain ⟨vf, Sf, m₂, hu₂, hm₂, he₂, hc₂', hi₂⟩ := ih (j+1)
        { v₁ with flag := (S₂.R count).head?.isSome } S₂ hc₂ (by simp at hN; omega) hi₁
        (by rw [hc₂])
      refine ⟨vf, Sf, 1+(m₁+1)+m₂+1, hu₂.trans hu₁, ?_,
        Exec.loop_true (by simpa using hflag) (Exec.seq hpop (Exec.seq he₁ hpeek)) he₂,
        hc₂', ?_⟩
      · simp only [List.length_cons]
        nlinarith only [hm₁, hm₂]
      · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hi₂
  have hpeek := Exec.act (body := body) (peekR count) (mk v S)
  rw [peekR_run] at hpeek
  obtain ⟨v', S', m, hu, hm, he, hc, hi⟩ := hloop (S.R count) 0
    { v with flag := (S.R count).head?.isSome } S rfl (by omega) hInv rfl
  exact ⟨v', S', 1+m, hu, by rw [hcount] at hm; omega,
    Exec.seq hpeek he, hc, by simpa only [hcount, Nat.zero_add] using hi⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
