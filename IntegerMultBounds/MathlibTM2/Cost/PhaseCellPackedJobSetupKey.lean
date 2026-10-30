module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCoreSetupKeys
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedJob

/-! Assign constructed jobs to the complete selected numerical key. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.NLogN.PhaseCellMatrix
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

/-- A job constructed for generated endpoints has exactly the production core
key. This includes the full-system fallback endpoint pair. -/
theorem packedJobSetupKey_eq_core {n ct A : ℕ} {i : Fin (Sizes.d n)} [NeZero (Sizes.s n i)]
    (r : PackedNormalizedJob A (Sizes.s n i))
    (hu : r.u ≤ Sizes.p n) (htarget : r.targetOut ≤ ct*Sizes.p n)
    (u : Fin (Sizes.p n+1)) (target : Fin (ct*Sizes.p n+1))
    (width band depth k : ℕ) (hU : r.u = u.val) (hTarget : r.targetOut = target.val)
    (hendpoints : (r.a,r.b) = coreHaloEndpoints (Sizes.s n i) width k band depth) :
    packedJobSetupKey r hu htarget = selectedCoreSetupKey n i ct u target width band depth k := by
  have ha := congrArg Prod.fst hendpoints
  have hb := congrArg Prod.snd hendpoints
  simp only [packedJobSetupKey,selectedCoreSetupKey,Prod.ext_iff,Fin.ext_iff]
  exact ⟨hU,hTarget,ha,hb⟩

/-- The executed job key belongs to the distinct generated setup family. -/
theorem packedJobSetupKey_mem_core {n ct A : ℕ} {i : Fin (Sizes.d n)} [NeZero (Sizes.s n i)]
    (r : PackedNormalizedJob A (Sizes.s n i))
    (hu : r.u ≤ Sizes.p n) (htarget : r.targetOut ≤ ct*Sizes.p n)
    (u : Fin (Sizes.p n+1)) (target : Fin (ct*Sizes.p n+1))
    (width band depth k : ℕ) (hU : r.u = u.val) (hTarget : r.targetOut = target.val)
    (hendpoints : (r.a,r.b) = coreHaloEndpoints (Sizes.s n i) width k band depth)
    (hk : k ∈ coreIndices (Sizes.s n i) width) :
    packedJobSetupKey r hu htarget ∈ selectedCoreSetupKeys n i ct u target width band depth := by
  rw [packedJobSetupKey_eq_core r hu htarget u target width band depth k hU hTarget hendpoints]
  exact Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hk)

end IntegerMultBounds.MathlibTM2.Cost
