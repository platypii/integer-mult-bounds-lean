module

public import IntegerMultBounds.MathlibTM2.M6.TranslatedLines

/-! Integer row witnesses for nonsingularity of translated prefix minors. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6

open IntegerMultBounds.Networks.Certificates.PR589
open IntegerMultBounds.Networks.Shared50ModularControl

/-- One generator and a row of a scaled left inverse for each pivot. -/
structure PrefixCertificate (d : ℕ) where
  lines : Fin d → Fin 111
  dual : Matrix (Fin d) (Fin d) ℤ

/-- Full-width prefix witnesses from generators of the selected label. -/
def HasPrefixWitness (label d : ℕ) : Prop :=
  ∃ lines : Fin d → Fin 111, (∀ i, (lines i).val ∈ Frames.labels label) ∧
    ∀ w : ℕ, IsUnit ((Matrix.of fun i (j : Fin d) => translatedEntry (lines i) j.val).map
      (Int.castRingHom (ZMod (prime ^ w))))

namespace PrefixCertificate

def minor {d : ℕ} (c : PrefixCertificate d) : Matrix (Fin d) (Fin d) ℤ :=
  Matrix.of fun i j => translatedEntry (c.lines i) j.val

/-- Independent scaling in each row keeps integral dual witnesses small. -/
def Checked {d : ℕ} (c : PrefixCertificate d) (label : ℕ) : Prop :=
  (∀ i, (c.lines i).val ∈ Frames.labels label) ∧
    ∀ i j, (c.dual * c.minor) i j ≠ 0 ↔ i = j

instance {d : ℕ} (c : PrefixCertificate d) (label : ℕ) : Decidable (c.Checked label) :=
  inferInstanceAs (Decidable ((∀ i, (c.lines i).val ∈ Frames.labels label) ∧ ∀ i j, (c.dual * c.minor) i j ≠ 0 ↔ i = j))

theorem det_ne_zero {d label : ℕ} {c : PrefixCertificate d} (h : c.Checked label) :
    c.minor.det ≠ 0 := by
  let M := c.dual * c.minor
  have diagonal : M = Matrix.diagonal (fun i => M i i) := by
    ext i j
    by_cases eq : i = j
    · subst j
      simp
    · simpa [Matrix.diagonal_apply_ne _ eq] using not_not.mp (fun nz => eq ((h.2 i j).mp nz))
  have nonzero : M.det ≠ 0 := by
    rw [diagonal, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (h.2 i i).mpr rfl
  exact right_ne_zero_of_mul (Matrix.det_mul c.dual c.minor ▸ nonzero)

theorem witness {d label : ℕ} {c : PrefixCertificate d} (dim : d ≤ 8)
    (h : c.Checked label) : HasPrefixWitness label d :=
  ⟨c.lines, h.1, translated_prefix_unit dim c.lines (det_ne_zero h)⟩

end PrefixCertificate
end IntegerMultBounds.MathlibTM2.M6
