import Mathlib.Logic.Equiv.Defs

/-! Abstract deterministic exceptional-address repair, for arbitrary types. -/

namespace IntegerMultBounds.Compact

variable {α : Type*} (S T : Equiv.Perm α) (bad : α → Prop)
  (hT : ∀ x, bad (T x) ↔ bad x)
  (agree : ∀ x, ¬bad x → S x = T x)

include hT agree

theorem inverse_agrees_off_bad (q : α) (hq : ¬bad q) :
    S.symm q = T.symm q := by
  have ht : ¬bad (T.symm q) := by
    intro h
    exact hq (by simpa using (hT (T.symm q)).mpr h)
  apply S.injective
  rw [S.apply_symm_apply, agree _ ht, T.apply_symm_apply]

theorem actual_preserves_bad (x : α) : bad (S x) ↔ bad x := by
  constructor
  · intro h
    by_contra hx
    rw [agree x hx] at h
    exact hx ((hT x).mp h)
  · intro hx
    by_contra hs
    have h := inverse_agrees_off_bad S T bad hT agree (S x) hs
    have ht : ¬bad (T.symm (S x)) := by
      intro hb
      exact hs (by simpa using (hT (T.symm (S x))).mpr hb)
    rw [S.symm_apply_apply] at h
    exact ht (h ▸ hx)

/-- Repair is identity off the exceptional set. -/
theorem correction_supported (q : α) (hq : ¬bad q) :
    T (S.symm q) = q := by
  rw [inverse_agrees_off_bad S T bad hT agree q hq, T.apply_symm_apply]

/-- Extracting and repairing precisely the bad destinations gives the ideal map. -/
theorem repair_exact [DecidablePred bad] (x : α) :
    (if bad (S x) then T (S.symm (S x)) else S x) = T x := by
  split
  · rw [S.symm_apply_apply]
  · rename_i h
    apply agree
    intro hx
    exact h ((actual_preserves_bad S T bad hT agree x).mpr hx)

end IntegerMultBounds.Compact
