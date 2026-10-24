module

public import IntegerMultBounds.MathlibTM2.Routing.MetadataJob

/-! A fixed count-tape loop over an indexed bank invariant. The index and bank
family occur only in the proof; the executed program reads its count tape. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def indexedCountLoopProgram (count : Fin T) (call : Pr P T Q A U) : Pr P T Q A U :=
  .seq (.act (peekR count)) (.loop (·.flag) (.seq call (.act (peekR count))))

theorem indexedCountLoop_exec (body : P → Pr P T Q A U)
    (count : Fin T) (call : Pr P T Q A U) (bank : ℕ → Stacks T A) (N price : ℕ)
    (hcount : ∀ i, ((bank i).R count).head?.isSome = decide (i < N))
    (hstep : ∀ i < N, ∀ u : HS T Q A U,
      ∃ (u' : HS T Q A U) (m : ℕ), u'.user = u.user ∧ m ≤ price ∧
        Exec body call (mk u (bank i)) m (mk u' (bank (i + 1))))
    (v : HS T Q A U) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ N * (price + 2) + 2 ∧
      Exec body (indexedCountLoopProgram count call) (mk v (bank 0)) m (mk v' (bank N)) := by
  have aux : ∀ j i, i + j = N → ∀ u : HS T Q A U, u.flag = decide (i < N) →
      ∃ (u' : HS T Q A U) (m : ℕ), u'.user = u.user ∧ m ≤ j * (price + 2) + 1 ∧
        Exec body (.loop (·.flag) (.seq call (.act (peekR count))))
          (mk u (bank i)) m (mk u' (bank N)) := by
    intro j
    induction j with
    | zero =>
      intro i hij u hf
      have hi : i = N := by omega
      subst i
      exact ⟨u, 1, rfl, by simp, Exec.loop_false (by simpa only [mk_var, lt_self_iff_false, decide_false] using hf)⟩
    | succ j ih =>
      intro i hij u hf
      have hi : i < N := by omega
      obtain ⟨u₁, m₁, hu₁, hm₁, hex₁⟩ := hstep i hi u
      let u₂ := { u₁ with flag := decide (i + 1 < N) }
      have hp : (peekR count : Act T Q A U).run (mk u₁ (bank (i + 1))) = mk u₂ (bank (i + 1)) := by
        simp only [peekR_run, hcount]
        rfl
      obtain ⟨u₃, m₃, hu₃, hm₃, hex₃⟩ := ih (i + 1) (by omega) u₂ rfl
      refine ⟨u₃, (m₁ + 1) + m₃ + 1, hu₃.trans hu₁, ?_, ?_⟩
      · simp only [Nat.add_mul, Nat.one_mul]
        omega
      · exact Exec.cast (Exec.loop_true
          (by simpa only [mk_var, hi, decide_true] using hf)
          (Exec.seq hex₁ (hp ▸ Exec.act (body := body) _ (mk u₁ (bank (i + 1))))) hex₃) (by omega) rfl
  let u := { v with flag := decide (0 < N) }
  have hp : (peekR count : Act T Q A U).run (mk v (bank 0)) = mk u (bank 0) := by
    simp only [peekR_run, hcount]
    rfl
  obtain ⟨v', m, hu, hm, hex⟩ := aux N 0 (by omega) u rfl
  exact ⟨v', 1 + m, hu, by omega,
    Exec.seq (hp ▸ Exec.act (body := body) _ (mk v (bank 0))) hex⟩

end IntegerMultBounds.MathlibTM2.Routing
