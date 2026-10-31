module

public import IntegerMultBounds.Machine.SharedBankStageInput

/-! One padded bank contains every common head and a stationary blank head.
Its reserve therefore bounds every other raw padding of that same bank. -/
@[expose] public section
namespace IntegerMultBounds.Machine.SharedBankStageInput
variable {t n a B : ℕ} {lo hi : ℤ}

theorem raw_margin_of_padding (x : Tapes t a) (h : t < n)
    (hm : ∀ j, lo+(B : ℕ) ≤ (raw x n).head j ∧ (raw x n).head j+(B : ℕ) ≤ hi) :
    ∀ m j, lo+(B : ℕ) ≤ (raw x m).head j ∧ (raw x m).head j+(B : ℕ) ≤ hi := by
  intro m j
  by_cases hj : j.val < t
  · have hh := hm ⟨j.val,lt_trans hj h⟩
    simpa only [raw,hj,↓reduceDIte] using hh
  · have hh := hm ⟨t,h⟩
    simpa only [raw,hj,lt_self_iff_false,↓reduceDIte] using hh

end IntegerMultBounds.Machine.SharedBankStageInput
