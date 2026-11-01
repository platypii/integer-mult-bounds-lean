module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop
public import IntegerMultBounds.MathlibTM2.StackNativeStock

/-! A counted loop shares one scratch reserve when completed bodies do not grow stock. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem countedLoop_exec_remaining_costs_within (count : Fin T) (p : Pr P T Q A U) (N : ℕ) (c : ℕ → ℕ)
    (Inv : ℕ → Stacks T A → Prop) (reserve : ℕ)
    (hstable : ∀ j S xs, Inv j S → Inv j { S with R := Function.update S.R count xs })
    (hstep : ∀ j < N, ∀ (v : HS T Q A U) S, Inv j S → (S.R count).length = N-(j+1) →
      ∃ v' S' m, v'.user = v.user ∧ m ≤ c j ∧
        (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+reserve)
          depth p (mk v S) m (mk v' S')) ∧
        S'.R count = S.R count ∧ Inv (j+1) S' ∧ mnSize (mk v' S') ≤ mnSize (mk v S))
    (v : HS T Q A U) (S : Stacks T A) (hcount : (S.R count).length = N) (hInv : Inv 0 S) :
    ∃ v' S' m, v'.user = v.user ∧ m ≤ (Finset.range N).sum (fun j => c j+3)+2 ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+reserve)
        depth (countedLoop count p) (mk v S) m (mk v' S')) ∧ S'.R count = [] ∧ Inv N S' := by
  have hloop : ∀ (xs : List (Fin (A+4))) (j : ℕ) (vi : HS T Q A U) Si,
      Si.R count = xs → j+xs.length = N → Inv j Si → vi.flag = xs.head?.isSome →
      ∃ vf Sf m, vf.user = vi.user ∧ m ≤ (Finset.range xs.length).sum (fun k => c (j+k)+3)+1 ∧
        (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk vi Si)+depth+reserve)
          depth (.loop (·.flag) (countedLoopBody count p)) (mk vi Si) m (mk vf Sf)) ∧
        Sf.R count = [] ∧ Inv (j+xs.length) Sf ∧ mnSize (mk vf Sf) ≤ mnSize (mk vi Si) := by
    intro xs
    induction xs with
    | nil =>
      intro j vi Si hxs _ hI hflag
      exact ⟨vi, Si, 1, rfl, by simp, (fun depth => ExecWithin.loop_false (by simpa using hflag) (by omega)), hxs,
        (by simpa using hI),le_refl _⟩
    | cons x xs ih =>
      intro j vi Si hxs hN hI hflag
      let S₁ : Stacks T A := { Si with R := Function.update Si.R count xs }
      have hpop : Exec body (.act (.pop (.rt count) (fun v _ => v) .done)) (mk vi Si) 1 (mk vi S₁) := by
        simpa [S₁, Action.run, hxs, update_rt] using
          (Exec.act (body := body) (.pop (.rt count) (fun v _ => v) .done) (mk vi Si))
      obtain ⟨v₁, S₂, m₁, hu₁, hm₁, he₁, hc₁, hi₁,hs₁⟩ := hstep j (by simp at hN; omega) vi S₁
        (hstable j Si xs hI) (by simp [S₁]; simp only [List.length_cons] at hN; omega)
      have hc₂ : S₂.R count = xs := by simpa [S₁] using hc₁
      have hpeek := Exec.act (body := body) (peekR count) (mk v₁ S₂)
      rw [peekR_run] at hpeek
      obtain ⟨vf, Sf, m₂, hu₂, hm₂, he₂, hc₂', hi₂,hs₂⟩ := ih (j+1)
        { v₁ with flag := (S₂.R count).head?.isSome } S₂ hc₂ (by simp at hN; omega) hi₁
        (by rw [hc₂])
      refine ⟨vf, Sf, 1+(m₁+1)+m₂+1, hu₂.trans hu₁, ?time,
        ?trace,hc₂',?inv,?stock⟩
      case trace =>
        intro depth
        have hp := mn_native_exec_within hpop 0 (by simp [mnNativePushBound,mnActPush]) depth
          (mnSize (mk vi Si)+depth) (by simp)
        have hsize : mnSize (mk vi S₁) ≤ mnSize (mk vi Si) := Nat.le_of_add_le_add_right hp.final
        let I : ℕ → Store (HΓ (T := T) A) (HS T Q A U) → Prop :=
          fun d z => mnSize z+d ≤ mnSize (mk vi Si)+depth+reserve
        have hp' := hp.mono (J := I) (by intro d z hz; exact hz.trans (Nat.le_add_right _ _))
        have ht₁ := (he₁ depth).mono (J := I) (by intro d z hz; dsimp only [I]; omega)
        have htpeek := mn_native_exec_within hpeek 0 (by simp [peekR,mnNativePushBound,mnActPush]) depth
          (mnSize (mk vi Si)+depth+reserve) (by simp only [Nat.zero_mul,Nat.add_zero]; omega)
        have ht₂ := (he₂ depth).mono (J := I) (by
          intro d z hz
          change mnSize z+d ≤ mnSize (mk v₁ S₂)+depth+reserve at hz
          dsimp only [I]
          omega)
        exact ExecWithin.loop_true (by simpa using hflag) (ExecWithin.seq hp' (ExecWithin.seq ht₁ htpeek)) ht₂
      case stock =>
        have hp := mn_native_exec_within hpop 0 (by simp [mnNativePushBound,mnActPush]) 0
          (mnSize (mk vi Si)) (by simp)
        have hs : mnSize (mk vi S₁) ≤ mnSize (mk vi Si) := by simpa using hp.final
        exact hs₂.trans (hs₁.trans hs)
      case time =>
        have hsum : (Finset.range (xs.length+1)).sum (fun k => c (j+k)+3) =
            (c j+3)+(Finset.range xs.length).sum (fun k => c (j+1+k)+3) := by
          rw [Finset.sum_range_succ']
          simp [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
        simp only [List.length_cons,hsum]
        omega
      case inv =>
        simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hi₂
  have hpeek := Exec.act (body := body) (peekR count) (mk v S)
  rw [peekR_run] at hpeek
  obtain ⟨v', S', m, hu, hm, he, hc, hi,_⟩ := hloop (S.R count) 0
    { v with flag := (S.R count).head?.isSome } S rfl (by omega) hInv rfl
  exact ⟨v', S', 1+m, hu, by rw [hcount] at hm; simp only [Nat.zero_add] at hm; omega,
    (fun depth => ExecWithin.seq
      (mn_native_exec_within hpeek 0 (by simp [peekR,mnNativePushBound,mnActPush]) depth
        (mnSize (mk v S)+depth+reserve) (by simp)) (he depth)), hc, by simpa only [hcount, Nat.zero_add] using hi⟩


theorem countedLoop_exec_costs_within (count : Fin T) (p : Pr P T Q A U) (N : ℕ) (c : ℕ → ℕ)
    (Inv : ℕ → Stacks T A → Prop) (reserve : ℕ)
    (hstable : ∀ j S xs, Inv j S → Inv j {S with R := Function.update S.R count xs})
    (hstep : ∀ j < N, ∀ (v : HS T Q A U) S, Inv j S →
      ∃ v' F m, v'.user = v.user ∧ m ≤ c j ∧
        (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+reserve)
          depth p (mk v S) m (mk v' F)) ∧ F.R count = S.R count ∧ Inv (j+1) F ∧
        mnSize (mk v' F) ≤ mnSize (mk v S))
    (v : HS T Q A U) (S : Stacks T A) (hcount : (S.R count).length = N) (hInv : Inv 0 S) :
    ∃ v' F m, v'.user = v.user ∧ m ≤ (Finset.range N).sum (fun j => c j+3)+2 ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+reserve)
        depth (countedLoop count p) (mk v S) m (mk v' F)) ∧ F.R count = [] ∧ Inv N F :=
  countedLoop_exec_remaining_costs_within count p N c Inv reserve hstable
    (fun j hj v S hI _ => hstep j hj v S hI) v S hcount hInv

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
