module

public import IntegerMultBounds.Machine.Frame
public import IntegerMultBounds.Machine.CompositionInvariant
public import IntegerMultBounds.Machine.RunInvariant

/-! Prefix invariants project through framed runs and compose through actual
sequential boundaries. Only the first component's real postcondition is needed
to establish readiness of the second. -/
@[expose] public section
namespace IntegerMultBounds.Machine
variable {t s q r a : ℕ}

theorem extend_run_inv (M : Program t q a) (extra : Tapes s a)
    {c : Config t q a} {d : Config (t+s) q a} {n : ℕ}
    (hr : run (extend M s) n (c.extend extra) = some d) :
    ∃ x, run M n c = some x ∧ d = x.extend extra := by
  induction n generalizing c with
  | zero =>
    simp only [run,Option.some.injEq] at hr
    exact ⟨c,rfl,hr.symm⟩
  | succ n ih =>
    change (step (extend M s) (c.extend extra)).bind (run (extend M s) n) = some d at hr
    rw [extend_step] at hr
    cases hs : step M c with
    | none => simp [hs] at hr
    | some y =>
      rw [hs,Option.map_some,Option.bind_some] at hr
      obtain ⟨x,hx,hd⟩ := ih hr
      exact ⟨x,by simp only [run,hs,Option.bind_some,hx],hd⟩

theorem RunInvariant.seq_tapes {M : Program t q a} {N : Program t r a}
    {pre mid : TapePred t a} {k : ℕ} (hM : HoareTime M pre mid k) (H : TapePred t a)
    (hleft : ∀ c, RunInvariant M pre c → H c.tapes)
    (hright : ∀ c, RunInvariant N mid c → H c.tapes)
    {c : Config t (q+r) a} (hc : RunInvariant (seq M N) pre c) : H c.tapes := by
  obtain ⟨v,hv,n,hr⟩ := hc
  have hinit : SeqInvariant (RunInvariant M pre) (RunInvariant N mid) (v.start (seq M N)) :=
    Or.inl ⟨v.start M,RunInvariant.initial hv,rfl⟩
  have hjoin : ∀ x, RunInvariant M pre x → Machine.step M x = none → RunInvariant N mid (x.tapes.start N) := by
    intro x hx hh
    exact RunInvariant.initial (RunInvariant.post hM hx hh)
  have h := hinit.run (fun _ _ hx hs => hx.step hs) (fun _ _ hx hs => hx.step hs) hjoin hr
  exact h.tapes H hleft hright

end IntegerMultBounds.Machine
