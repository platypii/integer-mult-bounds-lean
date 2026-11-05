module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerRawInput

/-! One arithmetic format covers retained scalars, geometry and boundary volume.
The format is selected from dimensions, independently of tape contents. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CommonClassGeometry

def callerCounterBound (p u l target s t B W N radius width : ℕ) : ℕ :=
  max (N*s*W) (p+u+l+target+s+t+B+W+3*radius+width+s*W)

def callerFormatWidth (B Vg Vr : ℕ) : ℕ := max B (max Vg Vr)

def canonicalCallerFormat (p u l target s t B W N radius width Vg Vr : ℕ) : ℕ :=
  max (callerFormatWidth B Vg Vr) (Nat.size (callerCounterBound p u l target s t B W N radius width))

theorem canonicalCallerFormat_fits (p u l target s t B W N radius width Vg Vr : ℕ)
    (hs : 1 ≤ s) (hW : 1 ≤ W) :
    let D := canonicalCallerFormat p u l target s t B W N radius width Vg Vr
    (width+2*radius < 2^D) ∧
    (∀ i, globalValues p u l target s t B W N radius width i < 2^D) ∧
    (∀ f, formatWidths B Vg Vr f ≤ D) ∧ s*W < 2^D := by
  let x := callerCounterBound p u l target s t B W N radius width
  let D := canonicalCallerFormat p u l target s t B W N radius width Vg Vr
  have hpower : x < 2^D := (Nat.lt_size_self x).trans_le
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (le_max_right _ _))
  have hscalar : p+u+l+target+s+t+B+W+3*radius+width+s*W ≤ x := le_max_right _ _
  have hvolume : N*s*W ≤ x := le_max_left _ _
  have hN : N ≤ N*s*W :=
    (Nat.le_mul_of_pos_right N hs).trans (Nat.le_mul_of_pos_right _ hW)
  have hgeometry : width+2*radius ≤ x := by omega
  have hvalues (i : Fin 11) : globalValues p u l target s t B W N radius width i ≤ x := by
    fin_cases i <;> simp [globalValues] <;> omega
  have hbits (f : Fin 3) : formatWidths B Vg Vr f ≤ D := by
    have hB : B ≤ callerFormatWidth B Vg Vr := le_max_left _ _
    have hVg : Vg ≤ callerFormatWidth B Vg Vr := (le_max_left _ _).trans (le_max_right _ _)
    have hVr : Vr ≤ callerFormatWidth B Vg Vr := (le_max_right _ _).trans (le_max_right _ _)
    have hformat : callerFormatWidth B Vg Vr ≤ D := le_max_left _ _
    fin_cases f <;> simp [formatWidths] <;> omega
  exact ⟨hgeometry.trans_lt hpower,fun i => (hvalues i).trans_lt hpower,hbits,
    (show s*W ≤ x by omega).trans_lt hpower⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
