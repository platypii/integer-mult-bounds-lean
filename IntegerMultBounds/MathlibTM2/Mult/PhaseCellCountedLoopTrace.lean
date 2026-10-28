module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop
public import IntegerMultBounds.MathlibTM2.StackCallResources

/-! A counted loop pays its boundary stock plus one body scratch allowance. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem countedLoop_exec_trace (count : Fin T) (p : Pr P T Q A U) (N : ℕ) (cost H : ℕ)
    (Inv : ℕ → Stacks T A → Prop)
    (hstable : ∀ j S xs, Inv j S → Inv j { S with R := Function.update S.R count xs })
    (hstep : ∀ j < N, ∀ (v : HS T Q A U) S, Inv j S → (S.R count).length = N-(j+1) →
      ∃ v' S' m, v'.user = v.user ∧ m ≤ cost ∧ Exec body p (mk v S) m (mk v' S') ∧
        S'.R count = S.R count ∧ Inv (j+1) S')
    (hstock : ∀ j ≤ N, ∀ S, Inv j S → (S.R count).length ≤ N →
      ∀ v : HS T Q A U, mnSize (mk v S) ≤ H)
    (v : HS T Q A U) (S : Stacks T A) (hcount : (S.R count).length = N) (hInv : Inv 0 S) :
    ∃ v' S' m, v'.user = v.user ∧ m ≤ (Finset.range N).sum (fun j => cost+3)+2 ∧
      Exec body (countedLoop count p) (mk v S) m (mk v' S') ∧ S'.R count = [] ∧ Inv N S' ∧
      ∀ c, mnProgPush p ≤ c → (∀ f, mnProgPush (body f) ≤ c) → ∀ depth,
      ExecWithin body (fun d z => mnSize z+d ≤ H+depth+(c+1)*cost) depth
        (countedLoop count p) (mk v S) m (mk v' S') := by
  have hloop : ∀ (xs : List (Fin (A+4))) (j : ℕ) (vi : HS T Q A U) Si,
      Si.R count = xs → j+xs.length = N → Inv j Si → vi.flag = xs.head?.isSome →
      ∃ vf Sf m, vf.user = vi.user ∧ m ≤ (Finset.range xs.length).sum (fun k => cost+3)+1 ∧
        Exec body (.loop (·.flag) (countedLoopBody count p)) (mk vi Si) m (mk vf Sf) ∧
        Sf.R count = [] ∧ Inv (j+xs.length) Sf ∧
        ∀ c, mnProgPush p ≤ c → (∀ f, mnProgPush (body f) ≤ c) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ H+depth+(c+1)*cost) depth
          (.loop (·.flag) (countedLoopBody count p)) (mk vi Si) m (mk vf Sf) := by
    intro xs
    induction xs with
    | nil =>
      intro j vi Si hxs hN hI hflag
      refine ⟨vi, Si, 1, rfl, by simp, Exec.loop_false (by simpa using hflag), hxs,
        by simpa using hI,?_⟩
      intro c hp hb depth
      exact .loop_false (by simpa using hflag)
        (by have hs := hstock j (by simp at hN; omega) Si hI
              (by simp [hxs]) vi
            change mnSize (mk vi Si)+depth ≤ _
            omega)
    | cons x xs ih =>
      intro j vi Si hxs hN hI hflag
      let S₁ : Stacks T A := { Si with R := Function.update Si.R count xs }
      have hpop : Exec body (.act (.pop (.rt count) (fun v _ => v) .done)) (mk vi Si) 1 (mk vi S₁) := by
        simpa [S₁, Action.run, hxs, update_rt] using
          (Exec.act (body := body) (.pop (.rt count) (fun v _ => v) .done) (mk vi Si))
      obtain ⟨v₁, S₂, m₁, hu₁, hm₁, he₁, hc₁, hi₁⟩ := hstep j (by simp at hN; omega) vi S₁
        (hstable j Si xs hI) (by simp [S₁]; simp only [List.length_cons] at hN; omega)
      have hc₂ : S₂.R count = xs := by simpa [S₁] using hc₁
      have hpeek := Exec.act (body := body) (peekR count) (mk v₁ S₂)
      rw [peekR_run] at hpeek
      obtain ⟨vf, Sf, m₂, hu₂, hm₂, he₂, hc₂', hi₂, ht₂⟩ := ih (j+1)
        { v₁ with flag := (S₂.R count).head?.isSome } S₂ hc₂ (by simp at hN; omega) hi₁
        (by rw [hc₂])
      refine ⟨vf, Sf, 1+(m₁+1)+m₂+1, hu₂.trans hu₁, ?_,
        Exec.loop_true (by simpa using hflag) (Exec.seq hpop (Exec.seq he₁ hpeek)) he₂,
        hc₂', ?_, ?_⟩
      · have hsum : (Finset.range (xs.length+1)).sum (fun k => cost+3) =
            (cost+3)+(Finset.range xs.length).sum (fun k => cost+3) := by
          rw [Finset.sum_range_succ']
          simp [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
        simp only [List.length_cons,hsum]
        omega
      · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hi₂
      · intro c hp hb depth
        have hs₀ := hstock j (by simp at hN; omega) Si hI (by simp [hxs]; simp at hN; omega) vi
        have hs₁ := hstock j (by simp at hN; omega) S₁ (hstable j Si xs hI)
          (by simp [S₁]; simp at hN; omega) vi
        have hs₂ := hstock (j+1) (by simp at hN; omega) S₂ hi₁
          (by rw [hc₂]; simp at hN; omega) v₁
        have htpop := mn_native_exec_within hpop 0 (by simp [mnNativePushBound,mnActPush]) depth
          (H+depth+(c+1)*cost) (by omega)
        have htbody := mn_exec_within he₁ hp hb depth
          (H+depth+(c+1)*cost) (by nlinarith)
        have htpeek := mn_native_exec_within hpeek 0
          (by simp [peekR,mnNativePushBound,mnActPush]) depth
          (H+depth+(c+1)*cost) (by omega)
        exact .loop_true (by simpa using hflag) (.seq htpop (.seq htbody htpeek))
          (ht₂ c hp hb depth)
  have hpeek := Exec.act (body := body) (peekR count) (mk v S)
  rw [peekR_run] at hpeek
  obtain ⟨v', S', m, hu, hm, he, hc, hi, ht⟩ := hloop (S.R count) 0
    { v with flag := (S.R count).head?.isSome } S rfl (by omega) hInv rfl
  refine ⟨v', S', 1+m, hu, by rw [hcount] at hm; omega,
    Exec.seq hpeek he, hc, by simpa only [hcount, Nat.zero_add] using hi,?_⟩
  intro c hp hb depth
  have hs := hstock 0 (Nat.zero_le _) S hInv hcount.le v
  have htpeek := mn_native_exec_within hpeek 0
    (by simp [peekR,mnNativePushBound,mnActPush]) depth
    (H+depth+(c+1)*cost) (by omega)
  exact .seq htpeek (ht c hp hb depth)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
