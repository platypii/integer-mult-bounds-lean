module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCanonicalInverseInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGridFamilyInverseBatch

/-! A singleton p-grid batch uses the ordinary binary scalar bank and its generated solver. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem haloVertices_full (s : ℕ) [NeZero s] : haloVertices s 0 s = Finset.univ := by
  ext i
  simp only [mem_haloVertices,Finset.mem_univ,iff_true]
  exact ⟨Nat.zero_le _,i.val_lt⟩

noncomputable def canonicalGridInput {A : ℕ} (p u l target s t : ℕ) [NeZero s]
    (F : ZMod s → GaussianInt) : Stacks 303 A :=
  {canonicalInverseInput p u l target s t F with R :=
    (Function.update (canonicalInverseInput (A := A) p u l target s t F).R (familyInverseCoreReg 246) [Node.tick])}

theorem canonicalGridInput_scalars {A : ℕ} (p u l target s t : ℕ) [NeZero s] (F : ZMod s → GaussianInt) :
    tblHolds familyInverseScalarReg (canonicalGridInput (A := A) p u l target s t F)
      (tblRho (inverseCallerWordWidth p u l target s t)
        (List.replicate (inverseCallerWordWidth p u l target s t) Node.tick) []
          (inverseInputScalars p u l target s t 0 s)) := by
  intro r
  dsimp only [canonicalGridInput]
  have hne : familyInverseScalarReg r ≠ familyInverseCoreReg 246 := familyInverseScalarReg_core r 246
  rw [Function.update_of_ne hne]
  exact canonicalInverseInput_scalars p u l target s t F r

theorem canonicalGridInput_core {A : ℕ} (p u l target s t : ℕ) [NeZero s] (F : ZMod s → GaussianInt)
    (i : Fin 263) (hi : i ≠ 110) (hc : i ≠ 246) :
    (canonicalGridInput (A := A) p u l target s t F).R (familyInverseCoreReg i) = [] := by
  dsimp only [canonicalGridInput]
  rw [Function.update_of_ne (familyInverseCoreReg_injective.ne hc)]
  exact canonicalInverseInput_core p u l target s t F i hi

@[simp] theorem canonicalGridInput_source {A : ℕ} (p u l target s t : ℕ) [NeZero s] (F : ZMod s → GaussianInt) :
    (canonicalGridInput (A := A) p u l target s t F).R 110 =
      cstream A (inverseFullInputWidth p u l target s t) (chirpLine s F) := by
  dsimp only [canonicalGridInput]
  rw [Function.update_of_ne (by decide : (110 : Fin 303) ≠ familyInverseCoreReg 246)]
  exact canonicalInverseInput_source p u l target s t F

@[simp] theorem canonicalGridInput_count {A : ℕ} (p u l target s t : ℕ) [NeZero s] (F : ZMod s → GaussianInt) :
    ((canonicalGridInput (A := A) p u l target s t F).R (familyInverseCoreReg 246)).length = 1 := by
  simp only [canonicalGridInput,Function.update_self,List.length_cons,List.length_nil]

@[simp] theorem canonicalGridInput_left {A : ℕ} (p u l target s t : ℕ) [NeZero s] (F : ZMod s → GaussianInt)
    (i : Fin 303) : (canonicalGridInput (A := A) p u l target s t F).L i = [] := rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
