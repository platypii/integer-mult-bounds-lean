module

public import IntegerMultBounds.Machine.RunInvariant
public import IntegerMultBounds.Machine.HoareHeadChange

/-! A known exact post-bank also bounds prefixes of a linear-time routine. -/
@[expose] public section
namespace IntegerMultBounds.Machine
variable {t q a : ℕ}

theorem RunInvariant.heads_eq_post {M : Program t q a} {before after : Tapes t a} {B : ℕ}
    (h : HoareTime M (· = before) (· = after) B) {c : Config t q a}
    (hc : RunInvariant M (· = before) c) :
    ∀ i, after.head i-(2*B : ℕ) ≤ c.head i ∧ c.head i ≤ after.head i+(2*B : ℕ) := by
  intro i
  have hp := hc.heads_eq h i
  have he := h.head_change i
  omega

end IntegerMultBounds.Machine
