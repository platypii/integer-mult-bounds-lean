module

public import IntegerMultBounds.NLogN.PhaseCellHaloMask
public import IntegerMultBounds.NLogN.PhaseCellHaloExterior

/-! Recovery's exterior guard is a fill followed by an ambient window clip. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def recoveryWindowLower (ambient : Bool) (s B a : ℕ) : ℕ :=
  if ambient then min s (B/2) else a-B/2

def recoveryWindowUpper (ambient : Bool) (s B b : ℕ) : ℕ :=
  if ambient then s-B/2 else min s (b+B/2)

theorem recoveryWindow_bounds (ambient : Bool) (s B a b : ℕ) (ha : a ≤ s) :
    recoveryWindowLower ambient s B a ≤ s ∧ recoveryWindowUpper ambient s B b ≤ s := by
  cases ambient <;> simp only [recoveryWindowLower,recoveryWindowUpper,Bool.false_eq_true,↓reduceIte] <;> omega

theorem recoveryWindows_spec (boundary : Bool) (s t B a b k : ℕ) (hb : b ≤ s) (hk : k < s) :
    (if recoveryWindowLower true s B a ≤ k ∧ k < recoveryWindowUpper true s B b then
      (if recoveryWindowLower false s B a ≤ k ∧ k < recoveryWindowUpper false s B b then
        boundary && haloInteriorAt s t B a b k else true) else false) =
      ((boundary && haloInteriorAt s t B a b k) || haloExteriorAt s (B/2) a b k) := by
  have hr : B/2 ≤ B := Nat.div_le_self _ _
  have hi : haloInteriorAt s t B a b k = true →
      recoveryWindowLower true s B a ≤ k ∧ k < recoveryWindowUpper true s B b := by
    intro h
    have hh := of_decide_eq_true h
    change a+B ≤ k ∧ k < b-B ∧ _ at hh
    change min s (B/2) ≤ k ∧ k < s-B/2
    omega
  have he : haloExteriorAt s (B/2) a b k =
      decide ((recoveryWindowLower true s B a ≤ k ∧ k < recoveryWindowUpper true s B b) ∧
        ¬(recoveryWindowLower false s B a ≤ k ∧ k < recoveryWindowUpper false s B b)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [haloExteriorAt,decide_eq_true_eq,recoveryWindowLower,recoveryWindowUpper,Bool.false_eq_true,↓reduceIte]
    omega
  rw [he]
  by_cases hamb : recoveryWindowLower true s B a ≤ k ∧ k < recoveryWindowUpper true s B b <;>
    by_cases hexp : recoveryWindowLower false s B a ≤ k ∧ k < recoveryWindowUpper false s B b <;>
    cases boundary <;> cases hI : haloInteriorAt s t B a b k <;> simp_all <;> omega

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
