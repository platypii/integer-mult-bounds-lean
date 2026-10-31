module

public import IntegerMultBounds.Machine.HeadTravel

/-! Exact execution contracts bound endpoint head displacement. -/
@[expose] public section
namespace IntegerMultBounds.Machine
variable {t q a : ℕ}

theorem HoareTime.head_change {M : Program t q a} {before after : Tapes t a} {B : ℕ}
    (h : HoareTime M (· = before) (· = after) B) :
    ∀ i, before.head i-B ≤ after.head i ∧ after.head i ≤ before.head i+B := by
  obtain ⟨n,c,hn,hr,_,hc⟩ := h before rfl
  intro i
  have ht := run_head_travel hr i
  have he := congrArg (fun v => v.head i) hc
  change c.head i = after.head i at he
  change before.head i-(n : ℤ) ≤ c.head i ∧ c.head i ≤ before.head i+(n : ℤ) at ht
  omega

end IntegerMultBounds.Machine
