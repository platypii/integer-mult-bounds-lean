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

theorem centered (D : ℕ) {x : ℤ} (hx : 0 ≤ x ∧ x ≤ 1) :
    -(D : ℤ)+(D : ℕ) ≤ x ∧ x+(D : ℕ) ≤ (D : ℤ)+1 := by omega

theorem centered_width (D : ℕ) :
    ((D : ℤ)+1+1-(-(D : ℤ))).toNat = 2*D+2 := by omega

end IntegerMultBounds.Machine.HeadMargin
