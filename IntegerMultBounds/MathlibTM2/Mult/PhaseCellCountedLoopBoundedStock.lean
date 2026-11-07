module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop
public import IntegerMultBounds.MathlibTM2.StackNativeStock

/-! A counted loop shares an absolute workspace reserve when dimension headers
change size between levels. Boundary stock need only be uniformly bounded. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem countedLoop_exec_bounded_stock (count : Fin T) (p : Pr P T Q A U) (N c B reserve : ℕ)
    (Inv : ℕ → Stacks T A → Prop)
    (hstable : ∀ j S xs, Inv j S → Inv j {S with R := Function.update S.R count xs})
    (hbound : ∀ j (v : HS T Q A U) S, Inv j S → (S.R count).length ≤ N → mnSize (mk v S) ≤ B)
    (hstep : ∀ j < N, ∀ (v : HS T Q A U) S, Inv j S → (S.R count).length = N-(j+1) →
      ∃ v' F m, v'.user = v.user ∧ m ≤ c ∧
        (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ B+depth+reserve)
          depth p (mk v S) m (mk v' F)) ∧ F.R count = S.R count ∧ Inv (j+1) F)
    (v : HS T Q A U) (S : Stacks T A) (hcount : (S.R count).length = N) (hInv : Inv 0 S) :
    ∃ v' F m, v'.user = v.user ∧ m ≤ N*(c+3)+2 ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ B+depth+reserve)
        depth (countedLoop count p) (mk v S) m (mk v' F)) ∧ F.R count = [] ∧ Inv N F := by
  have hloop : ∀ (xs : List (Fin (A+4))) (j : ℕ) (vi : HS T Q A U) Si,
      Si.R count = xs → j+xs.length = N → Inv j Si → vi.flag = xs.head?.isSome →
      ∃ vf Sf m, vf.user = vi.user ∧ m ≤ xs.length*(c+3)+1 ∧
        (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ B+depth+reserve)
          depth (.loop (·.flag) (countedLoopBody count p)) (mk vi Si) m (mk vf Sf)) ∧
        Sf.R count = [] ∧ Inv (j+xs.length) Sf := by
    intro xs
    induction xs with
    | nil =>
      intro j vi Si hxs hN hI hflag
      refine ⟨vi,Si,1,rfl,by simp,?_,hxs,by simpa using hI⟩
      intro depth
      apply ExecWithin.loop_false (by simpa using hflag)
      have hb := hbound j vi Si hI (by rw [hxs]; simp)
      omega
    | cons x xs ih =>
      intro j vi Si hxs hN hI hflag
      let S₁ : Stacks T A := {Si with R := Function.update Si.R count xs}
      have hpop : Exec body (.act (.pop (.rt count) (fun v _ => v) .done)) (mk vi Si) 1 (mk vi S₁) := by
        simpa [S₁,Action.run,hxs,update_rt] using
          (Exec.act (body := body) (.pop (.rt count) (fun v _ => v) .done) (mk vi Si))
      have hj : j < N := by simp only [List.length_cons] at hN; omega
      obtain ⟨v₁,S₂,m₁,hu₁,hm₁,he₁,hc₁,hi₁⟩ := hstep j hj vi S₁ (hstable j Si xs hI)
        (by simp [S₁]; simp only [List.length_cons] at hN; omega)
      have hc₂ : S₂.R count = xs := by simpa only [S₁,Function.update_self] using hc₁
      have hpeek := Exec.act (body := body) (peekR count) (mk v₁ S₂)
      rw [peekR_run] at hpeek
      obtain ⟨vf,Sf,m₂,hu₂,hm₂,he₂,hc₂',hi₂⟩ := ih (j+1)
        {v₁ with flag := (S₂.R count).head?.isSome} S₂ hc₂
        (by simp only [List.length_cons] at hN; omega) hi₁ (by rw [hc₂])
      refine ⟨vf,Sf,1+(m₁+1)+m₂+1,hu₂.trans hu₁,?_,?_,hc₂',?_⟩
      · simp only [List.length_cons]; nlinarith only [hm₁,hm₂]
      · intro depth
        have hb := hbound j vi Si hI (by rw [hxs]; simp only [List.length_cons] at hN ⊢; omega)
        have hp := mn_native_exec_within hpop 0 (by simp [mnNativePushBound,mnActPush]) depth
          (B+depth+reserve) (by simp; omega)
        have htpeek := mn_native_exec_within hpeek 0 (by simp [peekR,mnNativePushBound,mnActPush]) depth
          (B+depth+reserve) (by simpa using (he₁ depth).final)
        exact ExecWithin.loop_true (by simpa using hflag)
          (ExecWithin.seq hp (ExecWithin.seq (he₁ depth) htpeek)) (he₂ depth)
      · simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1] using hi₂
  have hpeek := Exec.act (body := body) (peekR count) (mk v S)
  rw [peekR_run] at hpeek
  obtain ⟨vf,F,m,hu,hm,he,hc,hI⟩ := hloop (S.R count) 0
    {v with flag := (S.R count).head?.isSome} S rfl (by omega) hInv rfl
  refine ⟨vf,F,1+m,hu,?_,?_,hc,by simpa only [hcount,Nat.zero_add] using hI⟩
  · rw [hcount] at hm; omega
  · intro depth
    have hb := hbound 0 v S hInv hcount.le
    exact ExecWithin.seq
      (mn_native_exec_within hpeek 0 (by simp [peekR,mnNativePushBound,mnActPush]) depth
        (B+depth+reserve) (by simp; omega)) (he depth)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
