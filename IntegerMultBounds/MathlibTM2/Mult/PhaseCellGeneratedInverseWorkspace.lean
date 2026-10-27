module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseInverseCaller
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedSingleComplex

/-! Place the shared-page core beside the existing raw-scalar bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

def generatedInverseSetupReg (i : Fin 264) : Fin 296 := ⟨i.val, by omega⟩

def generatedInverseCoreReg (i : Fin 256) : Fin 296 :=
  ⟨if i.val < 224 then i.val else i.val + 40, by split <;> omega⟩

theorem generatedInverseSetupReg_injective : Function.Injective generatedInverseSetupReg := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 296 => k.val) h)

theorem generatedInverseCoreReg_injective : Function.Injective generatedInverseCoreReg := by
  intro i j h
  have hval := congrArg (fun k : Fin 296 => k.val) h
  simp only [generatedInverseCoreReg] at hval
  split at hval <;> split at hval <;> apply Fin.ext <;> omega

theorem generatedInverseCoreReg_legacy (i : Fin 224) :
    generatedInverseCoreReg (couplingBoundaryReg (sharedPageRecoveryReg i)) = generatedInverseSetupReg (inverseCoreReg i) := by
  apply Fin.ext
  simp [generatedInverseCoreReg,couplingBoundaryReg,couplingCacheLegacyReg,sharedComplexBatchCoreReg, sharedPageRecoveryReg, generatedInverseSetupReg, inverseCoreReg]

theorem generatedInverseScalarReg_core (r : Fast.TableVM.TblR 25) (i : Fin 256) :
    generatedInverseSetupReg (inverseScalarReg r) ≠ generatedInverseCoreReg i := by
  intro he
  have hval := congrArg (fun k : Fin 296 => k.val) he
  cases r <;> simp only [generatedInverseSetupReg, inverseScalarReg, generatedInverseCoreReg] at hval <;>
    split at hval <;> omega

theorem generatedInverseCallerReg_cover (i : Fin 296) :
    (∃ k, generatedInverseCoreReg k = i) ∨
      ∃ r, generatedInverseSetupReg (inverseScalarReg r) = i := by
  by_cases hlo : i.val < 224
  · exact Or.inl ⟨⟨i.val, by omega⟩, Fin.ext (by simp [generatedInverseCoreReg, hlo])⟩
  by_cases hhi : i.val < 264
  · obtain ⟨k, hk⟩ | ⟨r, hr⟩ := inverseCallerReg_cover ⟨i.val, hhi⟩
    · have hv := congrArg (fun k : Fin 264 => k.val) hk
      simp only [inverseCoreReg] at hv
      omega
    · exact Or.inr ⟨r, Fin.ext (congrArg (fun k : Fin 264 => k.val) hr)⟩
  · exact Or.inl ⟨⟨i.val-40, by omega⟩, Fin.ext (by
      simp only [generatedInverseCoreReg]
      split <;> omega)⟩

def generatedInverseScalarReg (r : Fast.TableVM.TblR 25) : Fin 296 :=
  generatedInverseSetupReg (inverseScalarReg r)

def generatedInverseMasterPort (i : Fin 10) : Fin 296 :=
  generatedInverseSetupReg (inverseMasterPort i)

theorem generatedInverseScalarReg_injective : Function.Injective generatedInverseScalarReg :=
  generatedInverseSetupReg_injective.comp inverseScalarReg_injective

theorem generatedInverseMasterPort_injective : Function.Injective generatedInverseMasterPort :=
  generatedInverseSetupReg_injective.comp inverseMasterPort_injective

theorem generatedInverseScalarReg_master (i : Fin 10) (r : Fast.TableVM.TblR 25) :
    generatedInverseScalarReg r ≠ generatedInverseMasterPort i := by
  intro he
  exact inverseScalarReg_master i r (generatedInverseSetupReg_injective he)

noncomputable def generatedInverseCaller {Q A : ℕ} {P U : Type}
    (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 296 Q A U :=
  .seq (installInverseHeaders generatedInverseScalarReg generatedInverseMasterPort)
    (.seq (embProg generatedInverseCoreReg Empty.elim (generatedSingleComplex (P := Empty) recovery hR hQ))
      (releaseInverseHeaders generatedInverseScalarReg generatedInverseMasterPort))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
