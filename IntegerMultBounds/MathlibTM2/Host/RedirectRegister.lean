module

public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Redirect one owned register to a fresh destination without moving data. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host

def redirectRegister {T T' : ℕ} (e : Fin T → Fin T') (owned : Fin T) (dst : Fin T') (i : Fin T) : Fin T' :=
  if i = owned then dst else e i

@[simp] theorem redirectRegister_owned {T T' : ℕ} (e : Fin T → Fin T') (owned : Fin T) (dst : Fin T') :
    redirectRegister e owned dst owned = dst := by simp [redirectRegister]

theorem redirectRegister_off {T T' : ℕ} (e : Fin T → Fin T') (owned : Fin T) (dst : Fin T')
    (i : Fin T) (hi : i ≠ owned) : redirectRegister e owned dst i = e i := by simp [redirectRegister,hi]

theorem redirectRegister_injective {T T' : ℕ} (e : Fin T → Fin T') (he : Function.Injective e)
    (owned : Fin T) (dst : Fin T') (hoff : ∀ i, e i ≠ dst) :
    Function.Injective (redirectRegister e owned dst) := by
  intro i j h
  by_cases hi : i = owned <;> by_cases hj : j = owned
  · exact hi.trans hj.symm
  · simp only [redirectRegister,ite_eq_left hi,ite_eq_right hj] at h
    exact (hoff j h.symm).elim
  · simp only [redirectRegister,ite_eq_right hi,ite_eq_left hj] at h
    exact (hoff i h).elim
  · apply he
    simpa only [redirectRegister,ite_eq_right hi,ite_eq_right hj] using h

end IntegerMultBounds.MathlibTM2.Host
