module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyInverseCallerWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedInverseCaller

/-! A sparse ordinary family-dispatch bank: scalar table, ambient source and
replica count. The core/scalar cover determines every private register. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Node
variable {A : ℕ}

noncomputable def familyDispatchBank (H : Stacks 303 A) (B : ℕ) (wl : List (Fin (A+4)))
    (st : TblSt 25 A) (N : ℕ) (xs : List (Fin (A+4))) : Stacks 303 A :=
  let R := Function.extend familyInverseScalarReg (tblRho B wl [] st) (fun _ => [])
  {H with L := fun _ => [], R := (Function.update (Function.update R 110 xs)
    (familyInverseCoreReg 246) (List.replicate N tick))}

theorem familyDispatchBank_scalars (H : Stacks 303 A) (B : ℕ) (wl : List (Fin (A+4)))
    (st : TblSt 25 A) (N : ℕ) (xs : List (Fin (A+4))) :
    tblHolds familyInverseScalarReg (familyDispatchBank H B wl st N xs) (tblRho B wl [] st) := by
  intro r
  let R : Fin 303 → List (Fin (A+4)) := Function.extend familyInverseScalarReg (tblRho B wl [] st) (fun _ => [])
  change Function.update (Function.update R 110 xs) (familyInverseCoreReg 246) _ (familyInverseScalarReg r) = _
  have hc : familyInverseScalarReg r ≠ familyInverseCoreReg 246 := familyInverseScalarReg_core r 246
  have hs : familyInverseScalarReg r ≠ (110 : Fin 303) := familyInverseScalarReg_core r 110
  rw [Function.update_of_ne hc,Function.update_of_ne hs]
  exact familyInverseScalarReg_injective.extend_apply _ _ r

theorem familyDispatchBank_core (H : Stacks 303 A) (B : ℕ) (wl : List (Fin (A+4)))
    (st : TblSt 25 A) (N : ℕ) (xs : List (Fin (A+4))) (i : Fin 263) :
    (familyDispatchBank H B wl st N xs).R (familyInverseCoreReg i) =
      if i = 246 then List.replicate N tick else if i = 110 then xs else [] := by
  let R : Fin 303 → List (Fin (A+4)) := Function.extend familyInverseScalarReg (tblRho B wl [] st) (fun _ => [])
  have h110 : familyInverseCoreReg 110 = 110 := by decide
  by_cases hc : i = 246
  · subst i; simp [familyDispatchBank]
  by_cases hs : i = 110
  · subst i; simp [familyDispatchBank,h110,show (110 : Fin 303) ≠ familyInverseCoreReg 246 by decide]
  change Function.update (Function.update R 110 xs) (familyInverseCoreReg 246) _ (familyInverseCoreReg i) = _
  rw [Function.update_of_ne (familyInverseCoreReg_injective.ne hc),
    Function.update_of_ne (by simpa only [← h110] using familyInverseCoreReg_injective.ne hs)]
  rw [ite_eq_right hc,ite_eq_right hs]
  apply Function.extend_apply'
  rintro ⟨r,hr⟩
  exact familyInverseScalarReg_core r i hr

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
