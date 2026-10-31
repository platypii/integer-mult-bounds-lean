module

public import IntegerMultBounds.Machine.Placement

/-! Configuration invariants lift through exact tape-bank placement. The
complementary tape contents and heads remain fixed at every transition. -/
@[expose] public section
namespace IntegerMultBounds.Machine.Placement
variable {s u t q a : ℕ}

theorem placed_step_result (M : Program s q a) (e : Fin (s+u) ≃ Fin t)
    (v : Tapes t a) (c : Config s q a) :
    Machine.step (placed M e) (result e v c) = (Machine.step M c).map (result e v) := by
  rw [placed,result,reindex_step,extend_step]
  cases Machine.step M c <;> rfl

/-- The small invariant and a fixed spectator bank describe the whole bank. -/
def PlacedInvariant (e : Fin (s+u) ≃ Fin t) (v : Tapes t a)
    (I : Config s q a → Prop) (c : Config t q a) : Prop :=
  ∃ x, I x ∧ c = result e v x

theorem PlacedInvariant.initial {M : Program s q a} {e : Fin (s+u) ≃ Fin t}
    {v : Tapes t a} {I : Config s q a → Prop} (h : I ((active e v).start M)) :
    PlacedInvariant e v I (v.start (placed M e)) :=
  ⟨_,h,(start_view M e v).symm⟩

theorem PlacedInvariant.step {M : Program s q a} {e : Fin (s+u) ≃ Fin t}
    {v : Tapes t a} {I : Config s q a → Prop}
    (hpreserve : ∀ c d, I c → Machine.step M c = some d → I d)
    {c d : Config t q a} (hc : PlacedInvariant e v I c)
    (hs : Machine.step (placed M e) c = some d) : PlacedInvariant e v I d := by
  obtain ⟨x,hx,rfl⟩ := hc
  rw [placed_step_result] at hs
  cases he : Machine.step M x with
  | none => simp [he] at hs
  | some y =>
    simp only [he,Option.map_some,Option.some.injEq] at hs
    exact ⟨y,hpreserve x y hx he,hs.symm⟩

theorem PlacedInvariant.run {M : Program s q a} {e : Fin (s+u) ≃ Fin t}
    {v : Tapes t a} {I : Config s q a → Prop}
    (hpreserve : ∀ c d, I c → Machine.step M c = some d → I d)
    {c d : Config t q a} (hc : PlacedInvariant e v I c) {n : ℕ}
    (hrun : Machine.run (placed M e) n c = some d) : PlacedInvariant e v I d := by
  induction n generalizing c with
  | zero =>
    simp only [Machine.run,Option.some.injEq] at hrun
    subst d; exact hc
  | succ n ih =>
    simp only [Machine.run] at hrun
    cases hs : Machine.step (placed M e) c with
    | none => simp [hs] at hrun
    | some x =>
      rw [hs,Option.bind_some] at hrun
      exact ih (hc.step hpreserve hs) hrun

/-- Lift a predicate on complete tapes, including per-tape head intervals. -/
theorem PlacedInvariant.tapes {e : Fin (s+u) ≃ Fin t} {v : Tapes t a}
    {I : Config s q a → Prop} {c : Config t q a} (hc : PlacedInvariant e v I c)
    (H : TapePred t a) (h : ∀ x, I x → H (replace e v x.tapes)) : H c.tapes := by
  obtain ⟨x,hx,rfl⟩ := hc
  exact h x hx

theorem PlacedInvariant.extra {e : Fin (s+u) ≃ Fin t} {v : Tapes t a}
    {I : Config s q a → Prop} {c : Config t q a} (hc : PlacedInvariant e v I c) :
    extra e c.tapes = extra e v := by
  obtain ⟨x,_,rfl⟩ := hc
  exact extra_replace e v x.tapes

/-- Active head intervals and fixed spectator heads supply a whole-bank
interval bound for the host foreign-call stock theorem. -/
theorem PlacedInvariant.heads {e : Fin (s+u) ≃ Fin t} {v : Tapes t a}
    {I : Config s q a → Prop} {c : Config t q a} (hc : PlacedInvariant e v I c)
    (lo hi : Fin t → ℤ)
    (hactive : ∀ x, I x → ∀ i, lo (e (Fin.castAdd u i)) ≤ x.head i ∧
      x.head i ≤ hi (e (Fin.castAdd u i)))
    (hextra : ∀ i, lo (e (Fin.natAdd s i)) ≤ (Placement.extra e v).head i ∧
      (Placement.extra e v).head i ≤ hi (e (Fin.natAdd s i))) :
    ∀ i, lo i ≤ c.head i ∧ c.head i ≤ hi i := by
  apply hc.tapes (fun w => ∀ i, lo i ≤ w.head i ∧ w.head i ≤ hi i)
  intro x hx i
  obtain ⟨j,rfl⟩ := e.surjective i
  induction j using Fin.addCases with
  | left j => simpa only [replace,combine_head_active,Config.tapes] using hactive x hx j
  | right j => simpa only [replace,combine_head_extra] using hextra j

end IntegerMultBounds.Machine.Placement
