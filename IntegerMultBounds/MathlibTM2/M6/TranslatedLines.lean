module

public import IntegerMultBounds.MathlibTM2.M6.PrefixMinor
public import IntegerMultBounds.Networks.Certificates.PR589.Frames.Data

/-! Prefix minors drawn from the translated generators of the selected PR589 word. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6

open IntegerMultBounds.Networks.Certificates.PR589
open IntegerMultBounds.Networks.Shared50ModularControl

/-- Coefficient of degree `j` after translating a port polynomial by two. -/
def translatedEntry (line : Fin 111) (j : ℕ) : ℤ :=
  ((List.range 8).map fun k => (Frames.lines line.val).getD k 0 *
    (k.choose j : ℤ) * 2 ^ (k - j)).sum

private theorem entries_checked : (List.finRange 111).all (fun line =>
    (List.finRange 8).all fun j => decide ((translatedEntry line j.val).natAbs ≤ 1344)) = true := by
  decide +kernel

theorem translatedEntry_bound (line : Fin 111) (j : Fin 8) :
    (translatedEntry line j.val).natAbs ≤ 1344 := by
  have row := List.all_eq_true.mp entries_checked line (List.mem_finRange line)
  exact of_decide_eq_true (List.all_eq_true.mp row j (List.mem_finRange j))

/-- A nonsingular minor formed by the first `d` coefficients of selected word lines
is invertible at every tape radix. -/
theorem translated_prefix_unit {d : ℕ} (dim : d ≤ 8) (lines : Fin d → Fin 111) :
    let A : Matrix (Fin d) (Fin d) ℤ := Matrix.of fun i j => translatedEntry (lines i) j.val
    A.det ≠ 0 → ∀ w : ℕ, IsUnit (A.map (Int.castRingHom (ZMod (prime ^ w)))) := by
  intro A nonsingular w
  exact prefix_minor_unit dim A (fun i j => translatedEntry_bound (lines i) ⟨j.val,
    lt_of_lt_of_le j.isLt dim⟩) nonsingular w

end IntegerMultBounds.MathlibTM2.M6
