module

public import IntegerMultBounds.Machine.Hoare

/-! Preserved configuration invariants compose through the actual one-step
machine connection. Component invariants may depend on their finite control. -/
@[expose] public section
namespace IntegerMultBounds.Machine
variable {t q r a : ℕ}

/-- The active component's invariant, without exposing finite-state casts to
its mathematical or workspace proof. -/
def SeqInvariant (I : Config t q a → Prop) (J : Config t r a → Prop)
    (c : Config t (q+r) a) : Prop :=
  (∃ x, I x ∧ c = x.mapState (Fin.castAdd r)) ∨
    (∃ y, J y ∧ c = y.mapState (Fin.natAdd q))

theorem SeqInvariant.step {M : Program t q a} {N : Program t r a}
    {I : Config t q a → Prop} {J : Config t r a → Prop}
    (hI : ∀ c d, I c → Machine.step M c = some d → I d)
    (hJ : ∀ c d, J c → Machine.step N c = some d → J d)
    (hjoin : ∀ c, I c → Machine.step M c = none → J (c.tapes.start N))
    {c d : Config t (q+r) a} (hc : SeqInvariant I J c)
    (hs : Machine.step (seq M N) c = some d) : SeqInvariant I J d := by
  rcases hc with ⟨x,hx,rfl⟩ | ⟨y,hy,rfl⟩
  · cases hm : Machine.step M x with
    | none =>
      rw [seq_step_boundary M N hm,Option.some.injEq] at hs
      exact Or.inr ⟨x.tapes.start N,hjoin x hx hm,hs.symm⟩
    | some x' =>
      rw [seq_step_left M N hm,Option.some.injEq] at hs
      exact Or.inl ⟨x',hI x x' hx hm,hs.symm⟩
  · rw [seq_step_right] at hs
    cases hn : Machine.step N y with
    | none => simp [hn] at hs
    | some y' =>
      simp only [hn,Option.map_some,Option.some.injEq] at hs
      exact Or.inr ⟨y',hJ y y' hy hn,hs.symm⟩

theorem SeqInvariant.run {M : Program t q a} {N : Program t r a}
    {I : Config t q a → Prop} {J : Config t r a → Prop}
    (hI : ∀ c d, I c → Machine.step M c = some d → I d)
    (hJ : ∀ c d, J c → Machine.step N c = some d → J d)
    (hjoin : ∀ c, I c → Machine.step M c = none → J (c.tapes.start N))
    {c d : Config t (q+r) a} (hc : SeqInvariant I J c) {k : ℕ}
    (hrun : Machine.run (seq M N) k c = some d) : SeqInvariant I J d := by
  induction k generalizing c with
  | zero =>
    simp only [Machine.run,Option.some.injEq] at hrun
    subst d; exact hc
  | succ k ih =>
    simp only [Machine.run] at hrun
    cases hs : Machine.step (seq M N) c with
    | none => simp [hs] at hrun
    | some e =>
      rw [hs,Option.bind_some] at hrun
      exact ih (hc.step hI hJ hjoin hs) hrun

/-- Common tape/head bounds pass through either component and the connection. -/
theorem SeqInvariant.tapes {I : Config t q a → Prop} {J : Config t r a → Prop}
    {c : Config t (q+r) a} (hc : SeqInvariant I J c) (H : TapePred t a)
    (hI : ∀ x, I x → H x.tapes) (hJ : ∀ y, J y → H y.tapes) : H c.tapes := by
  rcases hc with ⟨x,hx,rfl⟩ | ⟨y,hy,rfl⟩
  · exact hI x hx
  · exact hJ y hy

end IntegerMultBounds.Machine
