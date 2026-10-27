module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseInverseCaller
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedSingleFamilyComplex

/-! Place the shared-page core beside the existing raw-scalar bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

def familyInverseSetupReg (i : Fin 264) : Fin 303 := ⟨i.val, by omega⟩

def familyInverseCoreReg (i : Fin 263) : Fin 303 :=
  ⟨if i.val < 224 then i.val else i.val + 40, by split <;> omega⟩

theorem familyInverseSetupReg_injective : Function.Injective familyInverseSetupReg := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 303 => k.val) h)

theorem familyInverseCoreReg_injective : Function.Injective familyInverseCoreReg := by
  intro i j h
  have hval := congrArg (fun k : Fin 303 => k.val) h
  simp only [familyInverseCoreReg] at hval
  split at hval <;> split at hval <;> apply Fin.ext <;> omega

theorem familyInverseCoreReg_legacy (i : Fin 224) :
    familyInverseCoreReg (familyBoundaryReg (sharedPageRecoveryReg i)) = familyInverseSetupReg (inverseCoreReg i) := by
  apply Fin.ext
  simp [familyInverseCoreReg,familyBoundaryReg,familyInverseLegacyReg,couplingBoundaryReg,couplingCacheLegacyReg,sharedComplexBatchCoreReg, sharedPageRecoveryReg, familyInverseSetupReg, inverseCoreReg]

theorem familyInverseScalarReg_core (r : Fast.TableVM.TblR 25) (i : Fin 263) :
    familyInverseSetupReg (inverseScalarReg r) ≠ familyInverseCoreReg i := by
  intro he
  have hval := congrArg (fun k : Fin 303 => k.val) he
  cases r <;> simp only [familyInverseSetupReg, inverseScalarReg, familyInverseCoreReg] at hval <;>
    split at hval <;> omega

theorem familyInverseCallerReg_cover (i : Fin 303) :
    (∃ k, familyInverseCoreReg k = i) ∨
      ∃ r, familyInverseSetupReg (inverseScalarReg r) = i := by
  by_cases hlo : i.val < 224
  · exact Or.inl ⟨⟨i.val, by omega⟩, Fin.ext (by simp [familyInverseCoreReg, hlo])⟩
  by_cases hhi : i.val < 264
  · obtain ⟨k, hk⟩ | ⟨r, hr⟩ := inverseCallerReg_cover ⟨i.val, hhi⟩
    · have hv := congrArg (fun k : Fin 264 => k.val) hk
      simp only [inverseCoreReg] at hv
      omega
    · exact Or.inr ⟨r, Fin.ext (congrArg (fun k : Fin 264 => k.val) hr)⟩
  · exact Or.inl ⟨⟨i.val-40, by omega⟩, Fin.ext (by
      simp only [familyInverseCoreReg]
      split <;> omega)⟩

def familyInverseScalarReg (r : Fast.TableVM.TblR 25) : Fin 303 :=
  familyInverseSetupReg (inverseScalarReg r)

def familyInverseMasterPort (i : Fin 10) : Fin 303 :=
  familyInverseSetupReg (inverseMasterPort i)

theorem familyInverseScalarReg_injective : Function.Injective familyInverseScalarReg :=
  familyInverseSetupReg_injective.comp inverseScalarReg_injective

theorem familyInverseMasterPort_injective : Function.Injective familyInverseMasterPort :=
  familyInverseSetupReg_injective.comp inverseMasterPort_injective

theorem familyInverseScalarReg_master (i : Fin 10) (r : Fast.TableVM.TblR 25) :
    familyInverseScalarReg r ≠ familyInverseMasterPort i := by
  intro he
  exact inverseScalarReg_master i r (familyInverseSetupReg_injective he)

noncomputable def familyInverseCaller {Q A : ℕ} {P U : Type}
    (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 303 Q A U :=
  .seq (installInverseHeaders familyInverseScalarReg familyInverseMasterPort)
    (.seq (embProg familyInverseCoreReg Empty.elim (generatedSingleFamilyComplex (P := Empty) recovery hR hQ))
      (releaseInverseHeaders familyInverseScalarReg familyInverseMasterPort))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
