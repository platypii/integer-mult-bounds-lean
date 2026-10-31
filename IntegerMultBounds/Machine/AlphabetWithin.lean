module

public import IntegerMultBounds.Machine.Alphabet
public import IntegerMultBounds.Machine.HoareWithin

/-! Alphabet encoding preserves every prefix head bound and exact runtime. -/
@[expose] public section
namespace IntegerMultBounds.Machine.Alphabet
variable {t q a b B : ℕ} {M : Program t q a} {pre post : TapePred t a}

theorem map_within (e : Encoding a b) (lo upper : ℤ)
    (h : HoareWithin M pre post B (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper)) :
    HoareWithin (program e M)
      (fun v => ∃ original, pre original ∧ v = mapTapes e original)
      (fun v => ∃ original, post original ∧ v = mapTapes e original) B
      (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
  rintro v ⟨original,hp,rfl⟩
  obtain ⟨n,hn,c,hr,hh,hpost⟩ := h original hp
  have hw := hr.simulation (G := fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) (mapConfig e)
    (by intro x y hs; rw [map_step,hs]; rfl) (by intro x hx; exact hx)
  exact ⟨n,hn,mapConfig e c,hw,(map_halt_iff e M c).mpr hh,c.tapes,hpost,rfl⟩

end IntegerMultBounds.Machine.Alphabet
