module

public import IntegerMultBounds.MathlibTM2.Host.Lift
public import IntegerMultBounds.Machine.HoareWithin

/-! State embedding preserves prefix bounds without changing any tape or head. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.Machine
variable {t q Q a B : ℕ} {M : Program t q a} {pre post : TapePred t a}

theorem HoareWithin.liftQ (h : q ≤ Q) (lo upper : ℤ)
    (hM : HoareWithin M pre post B (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper)) :
    HoareWithin (IntegerMultBounds.MathlibTM2.Host.liftQ M h) pre post B
      (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
  intro v hv
  obtain ⟨n,hn,c,hr,hh,hpost⟩ := hM v hv
  have hw := hr.simulation (G := fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) (fun z => z.mapState (Fin.castLE h))
    (by intro x y hs; rw [liftQ_step,hs]; rfl) (by intro x hx; exact hx)
  exact ⟨n,hn,c.mapState (Fin.castLE h),hw,by rw [liftQ_step,hh]; rfl,hpost⟩

end IntegerMultBounds.MathlibTM2.Host
