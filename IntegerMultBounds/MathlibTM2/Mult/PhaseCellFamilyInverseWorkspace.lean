module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyInitializedInterior
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCouplingSource

/-! The 256-register inverse and its two coupling caches keep their placement.
Seven additional ports hold the interior weight family and its active workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

def familyInverseLegacyReg (i : Fin 256) : Fin 263 := ⟨i.val,by omega⟩

theorem familyInverseLegacyReg_injective : Function.Injective familyInverseLegacyReg := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 263 => k.val) h)

def familyInverseReg (i : Fin 151) : Fin 263 :=
  ⟨if h : i.val < 144 then (couplingSourceReg ⟨i.val,h⟩).val else i.val+112,by
    split_ifs with h
    · exact Nat.lt_trans (couplingSourceReg ⟨i.val,h⟩).isLt (by decide)
    · omega⟩

theorem familyInverseReg_injective : Function.Injective familyInverseReg := by
  intro i j h
  have hv := congrArg (fun k : Fin 263 => k.val) h
  by_cases hi : i.val < 144 <;> by_cases hj : j.val < 144
  · simp only [familyInverseReg,dite_eq_left hi,dite_eq_left hj] at hv
    have he := couplingSourceReg_injective (Fin.ext hv)
    exact Fin.ext (congrArg (fun k : Fin 144 => k.val) he)
  · have hr := (couplingSourceReg ⟨i.val,hi⟩).isLt
    simp only [familyInverseReg,dite_eq_left hi,dite_eq_right hj] at hv
    omega
  · have hr := (couplingSourceReg ⟨j.val,hj⟩).isLt
    simp only [familyInverseReg,dite_eq_right hi,dite_eq_left hj] at hv
    omega
  · simp only [familyInverseReg,dite_eq_right hi,dite_eq_right hj] at hv
    apply Fin.ext
    omega

def familyInversePort (i : Fin 7) : Fin 263 := ⟨256+i.val,by omega⟩

theorem familyInverseLegacyReg_off (i : Fin 7) : ∀ j, familyInverseLegacyReg j ≠ familyInversePort i := by
  intro j he
  have hv := congrArg (fun k : Fin 263 => k.val) he
  dsimp [familyInverseLegacyReg,familyInversePort] at hv
  omega

theorem familyInverseReg_legacy (i : Fin 144) :
    familyInverseReg (weightFamilyLegacyReg i) = familyInverseLegacyReg (couplingSourceReg i) := by
  apply Fin.ext
  simp [familyInverseReg,weightFamilyLegacyReg,weightFamilyCoreReg,cachedGroupLegacyReg,familyInverseLegacyReg,i.isLt]

theorem familyInverseReg_port (i : Fin 7) :
    familyInverseReg ⟨144+i.val,by omega⟩ = familyInversePort i := by
  apply Fin.ext
  simp [familyInverseReg,familyInversePort,show ¬144+i.val < 144 by omega]
  omega

theorem familyInverse_legacy_view {A : ℕ} (S : Stacks 263 A) :
    weightFamilyLegacyBank (embStk familyInverseReg S) =
      embStk couplingSourceReg (embStk familyInverseLegacyReg S) := by
  refine Stacks.ext rfl rfl ?_ ?_
  · funext i
    exact congrArg S.L (familyInverseReg_legacy i)
  · funext i
    exact congrArg S.R (familyInverseReg_legacy i)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
