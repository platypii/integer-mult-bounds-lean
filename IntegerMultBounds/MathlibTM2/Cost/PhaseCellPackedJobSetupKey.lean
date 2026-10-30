module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupKeys
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedJob

/-! Assign constructed jobs to the complete selected numerical key. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

/-- Interval admissibility comes from the constructed job. Replica count and
movement geometry are not components of the numerical setup key. -/
def packedJobSetupKey {n ct A : ℕ} {i : Fin (Sizes.d n)} [NeZero (Sizes.s n i)]
    (r : PackedNormalizedJob A (Sizes.s n i))
    (hu : r.u ≤ Sizes.p n) (htarget : r.targetOut ≤ ct*Sizes.p n) : SelectedFamilyKey n i ct :=
  (⟨r.u,by omega⟩,⟨r.targetOut,by omega⟩,
    ⟨r.a,by have := r.bounds.hab; have := r.bounds.hbs; omega⟩,
    ⟨r.b,by have := r.bounds.hbs; omega⟩)

/-- Equality means equality of every varying numerical parameter, including
both endpoints; equal movement lengths alone do not establish reuse. -/
theorem packedJobSetupKey_eq_iff {n ct A : ℕ} {i : Fin (Sizes.d n)} [NeZero (Sizes.s n i)]
    (r r' : PackedNormalizedJob A (Sizes.s n i))
    (hu : r.u ≤ Sizes.p n) (htarget : r.targetOut ≤ ct*Sizes.p n)
    (hu' : r'.u ≤ Sizes.p n) (htarget' : r'.targetOut ≤ ct*Sizes.p n) :
    packedJobSetupKey r hu htarget = packedJobSetupKey r' hu' htarget' ↔
      r.u = r'.u ∧ r.targetOut = r'.targetOut ∧ r.a = r'.a ∧ r.b = r'.b := by
  simp only [packedJobSetupKey,Prod.ext_iff,Fin.ext_iff]

end IntegerMultBounds.MathlibTM2.Cost
