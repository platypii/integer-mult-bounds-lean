module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSelectedFamilyInverseCaller

/-! The ordinary raw input bank of the executed full-line inverse, constructed from its scalar inputs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

noncomputable def inverseFullInputWidth (p u l target s t : ℕ) [NeZero s] : ℕ :=
  executionWidth p l (initialSchurTarget p u
    (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
      (haloBoundary s t (PhaseCellBand.width p u) 0 s).card) 2) 2

noncomputable def inverseFullInputPrecision (p u l target s t : ℕ) [NeZero s] : ℕ :=
  executionPrecision p l (initialSchurTarget p u
    (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
      (haloBoundary s t (PhaseCellBand.width p u) 0 s).card) 2) 2

noncomputable def canonicalInverseInput {A : ℕ} (p u l target s t : ℕ) [NeZero s]
    (F : ZMod s → GaussianInt) : Stacks 303 A :=
  let W := inverseCallerWordWidth p u l target s t
  let bank := Function.extend familyInverseScalarReg
    (tblRho W (List.replicate W Node.tick) [] (inverseInputScalars p u l target s t 0 s)) (fun _ => [])
  ⟨[],[],fun _ => [],Function.update bank 110 (cstream A (inverseFullInputWidth p u l target s t) (chirpLine s F))⟩

theorem canonicalInverseInput_scalars {A : ℕ} (p u l target s t : ℕ) [NeZero s] (F : ZMod s → GaussianInt) :
    tblHolds familyInverseScalarReg (canonicalInverseInput (A := A) p u l target s t F)
      (tblRho (inverseCallerWordWidth p u l target s t)
        (List.replicate (inverseCallerWordWidth p u l target s t) Node.tick) []
          (inverseInputScalars p u l target s t 0 s)) := by
  intro r
  dsimp only [canonicalInverseInput]
  have hne : familyInverseScalarReg r ≠ (110 : Fin 303) := familyInverseScalarReg_core r 110
  rw [Function.update_of_ne hne]
  exact familyInverseScalarReg_injective.extend_apply _ _ r

theorem canonicalInverseInput_core {A : ℕ} (p u l target s t : ℕ) [NeZero s] (F : ZMod s → GaussianInt)
    (i : Fin 263) (hi : i ≠ 110) :
    (canonicalInverseInput (A := A) p u l target s t F).R (familyInverseCoreReg i) = [] := by
  have h110 : familyInverseCoreReg i ≠ 110 := by
    intro he
    exact hi (familyInverseCoreReg_injective he)
  dsimp only [canonicalInverseInput]
  rw [Function.update_of_ne h110]
  apply Function.extend_apply'
  rintro ⟨r,hr⟩
  exact familyInverseScalarReg_core r i hr

@[simp] theorem canonicalInverseInput_source {A : ℕ} (p u l target s t : ℕ) [NeZero s] (F : ZMod s → GaussianInt) :
    (canonicalInverseInput (A := A) p u l target s t F).R 110 =
      cstream A (inverseFullInputWidth p u l target s t) (chirpLine s F) := by
  simp only [canonicalInverseInput,Function.update_self]

@[simp] theorem canonicalInverseInput_left {A : ℕ} (p u l target s t : ℕ) [NeZero s] (F : ZMod s → GaussianInt)
    (i : Fin 303) : (canonicalInverseInput (A := A) p u l target s t F).L i = [] := rfl

@[simp] theorem canonicalInverseInput_output {A : ℕ} (p u l target s t : ℕ) [NeZero s] (F : ZMod s → GaussianInt) :
    (canonicalInverseInput (A := A) p u l target s t F).R 132 = [] :=
  canonicalInverseInput_core p u l target s t F 132 (by decide)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
