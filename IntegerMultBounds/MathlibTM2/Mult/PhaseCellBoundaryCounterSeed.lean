module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryCropMetadata

/-! The boundary metadata table starts with three dimensions and zero working
variables; its size follows from the ambient encoded-volume bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.BoundaryCropMetadata
open IntegerMultBounds.MathlibTM2.Fast.TableVM

def seed (A s width W : ℕ) : TblSt 9 A :=
  ⟨![s,width,W,0,0,0,0,0,0],[]⟩

theorem seed_inputs (A s width W : ℕ) :
    (seed A s width W).val 0 = s ∧ (seed A s width W).val 1 = width ∧
      (seed A s width W).val 2 = W := by simp [seed]

theorem seed_working_zero (A s width W : ℕ) (i : Fin 9) (hi : 3 ≤ i.val) :
    (seed A s width W).val i = 0 := by
  fin_cases i <;> simp_all [seed]

theorem seed_fits (A D s width W : ℕ) (hs : 1 ≤ s) (hW : 1 ≤ W)
    (hwidth : width ≤ s) (hfit : s*W < 2^D) :
    ∀ i, (seed A s width W).val i < 2^D := by
  have hsW : s ≤ s*W := by nlinarith
  have hWs : W ≤ s*W := by nlinarith
  intro i
  fin_cases i <;> simp [seed]
  all_goals omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.BoundaryCropMetadata
