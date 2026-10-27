module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseInverseCaller
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageClosedComplex

/-! Place the shared-page core beside the existing raw-scalar bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

def sharedInverseSetupReg (i : Fin 264) : Fin 280 := ⟨i.val, by omega⟩

def sharedInverseCoreReg (i : Fin 240) : Fin 280 :=
  ⟨if i.val < 224 then i.val else i.val + 40, by split <;> omega⟩

theorem sharedInverseSetupReg_injective : Function.Injective sharedInverseSetupReg := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 280 => k.val) h)

theorem sharedInverseCoreReg_injective : Function.Injective sharedInverseCoreReg := by
  intro i j h
  have hval := congrArg (fun k : Fin 280 => k.val) h
  simp only [sharedInverseCoreReg] at hval
  split at hval <;> split at hval <;> apply Fin.ext <;> omega

theorem sharedInverseCoreReg_legacy (i : Fin 224) :
    sharedInverseCoreReg (sharedPageRecoveryReg i) = sharedInverseSetupReg (inverseCoreReg i) := by
  apply Fin.ext
  simp [sharedInverseCoreReg, sharedPageRecoveryReg, sharedInverseSetupReg, inverseCoreReg]

theorem sharedInverseScalarReg_core (r : Fast.TableVM.TblR 25) (i : Fin 240) :
    sharedInverseSetupReg (inverseScalarReg r) ≠ sharedInverseCoreReg i := by
  intro he
  have hval := congrArg (fun k : Fin 280 => k.val) he
  cases r <;> simp only [sharedInverseSetupReg, inverseScalarReg, sharedInverseCoreReg] at hval <;>
    split at hval <;> omega

theorem sharedInverseCallerReg_cover (i : Fin 280) :
    (∃ k, sharedInverseCoreReg k = i) ∨
      ∃ r, sharedInverseSetupReg (inverseScalarReg r) = i := by
  by_cases hlo : i.val < 224
  · exact Or.inl ⟨⟨i.val, by omega⟩, Fin.ext (by simp [sharedInverseCoreReg, hlo])⟩
  by_cases hhi : i.val < 264
  · obtain ⟨k, hk⟩ | ⟨r, hr⟩ := inverseCallerReg_cover ⟨i.val, hhi⟩
    · have hv := congrArg (fun k : Fin 264 => k.val) hk
      simp only [inverseCoreReg] at hv
      omega
    · exact Or.inr ⟨r, Fin.ext (congrArg (fun k : Fin 264 => k.val) hr)⟩
  · exact Or.inl ⟨⟨i.val-40, by omega⟩, Fin.ext (by
      simp only [sharedInverseCoreReg]
      split <;> omega)⟩

def sharedInverseScalarReg (r : Fast.TableVM.TblR 25) : Fin 280 :=
  sharedInverseSetupReg (inverseScalarReg r)

def sharedInverseMasterPort (i : Fin 10) : Fin 280 :=
  sharedInverseSetupReg (inverseMasterPort i)

theorem sharedInverseScalarReg_injective : Function.Injective sharedInverseScalarReg :=
  sharedInverseSetupReg_injective.comp inverseScalarReg_injective

theorem sharedInverseMasterPort_injective : Function.Injective sharedInverseMasterPort :=
  sharedInverseSetupReg_injective.comp inverseMasterPort_injective

theorem sharedInverseScalarReg_master (i : Fin 10) (r : Fast.TableVM.TblR 25) :
    sharedInverseScalarReg r ≠ sharedInverseMasterPort i := by
  intro he
  exact inverseScalarReg_master i r (sharedInverseSetupReg_injective he)

noncomputable def sharedInverseCaller {Q A : ℕ} {P U : Type}
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 280 Q A U :=
  .seq (installInverseHeaders sharedInverseScalarReg sharedInverseMasterPort)
    (.seq (embProg sharedInverseCoreReg Empty.elim (sharedPageClosedComplex (P := Empty) hR hQ))
      (releaseInverseHeaders sharedInverseScalarReg sharedInverseMasterPort))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
