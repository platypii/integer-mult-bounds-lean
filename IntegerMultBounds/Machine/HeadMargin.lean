module

public import IntegerMultBounds.Machine.HoareWithin

/-! Reserve arithmetic is proved on arbitrary heads and budgets, before
instantiating concrete machine banks or closed initialization costs. -/
@[expose] public section
namespace IntegerMultBounds.Machine.HeadMargin

theorem weaken {B C : ℕ} {lo upper x : ℤ} (h : B ≤ C)
    (hm : lo+(C : ℕ) ≤ x ∧ x+(C : ℕ) ≤ upper) :
    lo+(B : ℕ) ≤ x ∧ x+(B : ℕ) ≤ upper := by omega

theorem after {S B C : ℕ} {lo upper x y : ℤ} (h : S+B ≤ C)
    (ht : x-(S : ℕ) ≤ y ∧ y ≤ x+(S : ℕ))
    (hm : lo+(C : ℕ) ≤ x ∧ x+(C : ℕ) ≤ upper) :
    lo+(B : ℕ) ≤ y ∧ y+(B : ℕ) ≤ upper := by omega

theorem before {S B C : ℕ} {lo upper x y : ℤ} (h : S+B ≤ C)
    (ht : x-(S : ℕ) ≤ y ∧ y ≤ x+(S : ℕ))
    (hm : lo+(C : ℕ) ≤ y ∧ y+(C : ℕ) ≤ upper) :
    lo+(B : ℕ) ≤ x ∧ x+(B : ℕ) ≤ upper := by omega

end IntegerMultBounds.Machine.HeadMargin
