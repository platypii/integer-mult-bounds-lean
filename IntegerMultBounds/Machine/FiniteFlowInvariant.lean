module

public import IntegerMultBounds.Machine.FiniteFlow

/-! Configuration invariants for finite block controllers, including back
edges. Mathematical tape bounds are independent of the encoding of control. -/
@[expose] public section
namespace IntegerMultBounds.Machine.FiniteFlow
noncomputable section
variable {N t a : ℕ} {states : Fin N → ℕ}

def Invariant (I : ∀ pc, Config t (states pc) a → Prop)
    (c : Config t (Fintype.card (Control states)) a) : Prop :=
  ∃ pc x, I pc x ∧ c = x.mapState (embed states pc)

theorem Invariant.step {family : ∀ pc, Program t (states pc) a} {next : Next states}
    {entry : Fin N} {I : ∀ pc, Config t (states pc) a → Prop}
    (hblock : ∀ pc c d, I pc c → Machine.step (family pc) c = some d → I pc d)
    (hedge : ∀ pc c pc', I pc c → Machine.step (family pc) c = none →
      next pc c.state = some pc' → I pc' (c.tapes.start (family pc')))
    {c d : Config t (Fintype.card (Control states)) a} (hc : Invariant I c)
    (hs : Machine.step (program family next entry) c = some d) : Invariant I d := by
  obtain ⟨pc,x,hx,rfl⟩ := hc
  cases hm : Machine.step (family pc) x with
  | some y =>
    have hb := block_run family next entry pc 1 x y (by simpa only [run_one] using hm)
    simp only [run_one] at hb
    rw [hb,Option.some.injEq] at hs
    exact ⟨pc,y,hblock pc x y hx hm,hs.symm⟩
  | none =>
    cases hn : next pc x.state with
    | none => rw [halt family next entry pc x hm hn] at hs; cases hs
    | some pc' =>
      rw [jump family next entry pc pc' x hm hn,Option.some.injEq] at hs
      exact ⟨pc',x.tapes.start (family pc'),hedge pc x pc' hx hm hn,hs.symm⟩

theorem Invariant.run {family : ∀ pc, Program t (states pc) a} {next : Next states}
    {entry : Fin N} {I : ∀ pc, Config t (states pc) a → Prop}
    (hblock : ∀ pc c d, I pc c → Machine.step (family pc) c = some d → I pc d)
    (hedge : ∀ pc c pc', I pc c → Machine.step (family pc) c = none →
      next pc c.state = some pc' → I pc' (c.tapes.start (family pc')))
    {c d : Config t (Fintype.card (Control states)) a} (hc : Invariant I c) {k : ℕ}
    (hrun : Machine.run (program family next entry) k c = some d) : Invariant I d := by
  induction k generalizing c with
  | zero =>
    simp only [Machine.run,Option.some.injEq] at hrun
    subst d; exact hc
  | succ k ih =>
    simp only [Machine.run] at hrun
    cases hs : Machine.step (program family next entry) c with
    | none => simp [hs] at hrun
    | some e =>
      rw [hs,Option.bind_some] at hrun
      exact ih (hc.step hblock hedge hs) hrun

theorem Invariant.tapes {I : ∀ pc, Config t (states pc) a → Prop}
    {c : Config t (Fintype.card (Control states)) a} (hc : Invariant I c)
    (H : TapePred t a) (hblock : ∀ pc x, I pc x → H x.tapes) : H c.tapes := by
  obtain ⟨pc,x,hx,rfl⟩ := hc
  exact hblock pc x hx

end
end IntegerMultBounds.Machine.FiniteFlow
