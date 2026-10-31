module

public import IntegerMultBounds.Machine.HoareWithinFrame
public import IntegerMultBounds.Machine.Placement

/-! Exact physical placement carries prefix bounds over arbitrary stationary
complementary tapes, with unchanged runtime and the original replacement law. -/
@[expose] public section
namespace IntegerMultBounds.Machine.HoareWithin
variable {s u t q a B : ℕ} {M : Program s q a} {pre post : TapePred s a} {lo hi : ℤ}

theorem placed_heads_at (h : HoareWithin M pre post B (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi))
    (e : Fin (s+u) ≃ Fin t) (v : Tapes t a) (hp : pre (Placement.active e v))
    (hframe : ∀ j, lo ≤ (Placement.extra e v).head j ∧ (Placement.extra e v).head j ≤ hi) :
    HoareWithin (Placement.placed M e) (· = v)
      (fun output => ∃ w, post w ∧ output = Placement.replace e v w) B
      (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  intro input hv
  subst input
  obtain ⟨n,hn,c,hr,hh,hpost⟩ := h (Placement.active e v) hp
  have hw := hr.simulation (N := Placement.placed M e)
    (G := fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) (fun c => Placement.result e v c)
    (by
      intro x y hs
      simp only [Placement.placed,Placement.result,reindex_step,extend_step,hs,Option.map_some])
    (by
      intro x hx j
      change lo ≤ (x.tapes.append (Placement.extra e v)).head (e.symm j) ∧
        (x.tapes.append (Placement.extra e v)).head (e.symm j) ≤ hi
      generalize e.symm j = i
      induction i using Fin.addCases with
      | left i => simpa only [Tapes.append,Fin.addCases_left] using hx i
      | right i => simpa only [Tapes.append,Fin.addCases_right] using hframe i)
  rw [Placement.start_view] at hw
  exact ⟨n,hn,Placement.result e v c,hw,Placement.placed_halt M e v hh,c.tapes,hpost,rfl⟩

end IntegerMultBounds.Machine.HoareWithin
