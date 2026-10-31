module

public import IntegerMultBounds.Machine.FiniteFlowInvariant
public import IntegerMultBounds.Machine.RunInvariant

/-! Block execution contracts supply controller invariants without re-proving
internal transitions. Terminal states and tape postconditions both pass through
actual jumps, including recursive back edges. -/
@[expose] public section
namespace IntegerMultBounds.Machine.FiniteFlow
noncomputable section
variable {N t a : ℕ} {states : Fin N → ℕ}
  {family : ∀ pc, Program t (states pc) a} {next : Next states} {entry : Fin N}
  {pre : Fin N → TapePred t a}
  {post : ∀ pc, Config t (states pc) a → Prop}

def RunFamilyInvariant (family : ∀ pc, Program t (states pc) a) (pre : Fin N → TapePred t a) :=
  Invariant (fun pc => RunInvariant (family pc) (pre pc))

theorem RunFamilyInvariant.initial {v : Tapes t a} (hv : pre entry v) :
    RunFamilyInvariant family pre (v.start (program family next entry)) :=
  ⟨entry,v.start (family entry),RunInvariant.initial hv,rfl⟩

theorem RunFamilyInvariant.step
    (hcomplete : ∀ pc v, pre pc v → ∃ n z, run (family pc) n (v.start (family pc)) = some z ∧
      Machine.step (family pc) z = none ∧ post pc z)
    (hedge : ∀ pc z pc', post pc z → next pc z.state = some pc' → pre pc' z.tapes)
    {c d : Config t (Fintype.card (Control states)) a} (hc : RunFamilyInvariant family pre c)
    (hs : Machine.step (program family next entry) c = some d) : RunFamilyInvariant family pre d := by
  apply Invariant.step (I := fun pc => RunInvariant (family pc) (pre pc)) (family := family) (next := next) (fun _ _ _ h hs => RunInvariant.step h hs) ?_ hc hs
  intro pc z pc' hz hh he
  exact RunInvariant.initial (hedge pc z pc' (hz.post_config (hcomplete pc) hh) he)

theorem RunFamilyInvariant.run
    (hcomplete : ∀ pc v, pre pc v → ∃ n z, Machine.run (family pc) n (v.start (family pc)) = some z ∧
      Machine.step (family pc) z = none ∧ post pc z)
    (hedge : ∀ pc z pc', post pc z → next pc z.state = some pc' → pre pc' z.tapes)
    {c d : Config t (Fintype.card (Control states)) a} (hc : RunFamilyInvariant family pre c) {n : ℕ}
    (hrun : Machine.run (program family next entry) n c = some d) : RunFamilyInvariant family pre d := by
  apply Invariant.run (I := fun pc => RunInvariant (family pc) (pre pc)) (family := family) (next := next) (fun _ _ _ h hs => RunInvariant.step h hs) ?_ hc hrun
  intro pc z pc' hz hh he
  exact RunInvariant.initial (hedge pc z pc' (hz.post_config (hcomplete pc) hh) he)

/-- A common head interval is preserved across tape-preserving controller
jumps; each block only supplies bounds for its own reachable configurations. -/
theorem RunFamilyInvariant.heads
    (lo hi : Fin t → ℤ)
    (hblock : ∀ pc z, RunInvariant (family pc) (pre pc) z → ∀ i, lo i ≤ z.head i ∧ z.head i ≤ hi i)
    {c : Config t (Fintype.card (Control states)) a} (hc : RunFamilyInvariant family pre c) :
    ∀ i, lo i ≤ c.head i ∧ c.head i ≤ hi i := by
  exact hc.tapes (fun v => ∀ i, lo i ≤ v.head i ∧ v.head i ≤ hi i) hblock

end
end IntegerMultBounds.Machine.FiniteFlow
