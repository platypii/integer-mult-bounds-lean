module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallInverseHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedInverse

/-! The 224-register retained solver and its disjoint 40-register scalar setup bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast.TableVM

def inverseCoreReg (i : Fin 224) : Fin 264 := ⟨i.val,by omega⟩

theorem inverseCoreReg_injective : Function.Injective inverseCoreReg := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 264 => k.val) h)

def inverseScalarReg : TblR 25 → Fin 264
  | .v i => ⟨224+i.val,by omega⟩
  | .wr => 249
  | .wn => 250
  | .acc => 251
  | .z i => ⟨252+i.val,by omega⟩

theorem inverseScalarReg_injective : Function.Injective inverseScalarReg := by
  intro i j h
  have hh := congrArg (fun k : Fin 264 => k.val) h
  cases i <;> cases j <;> simp only [inverseScalarReg] at hh <;> first
    | rfl
    | (congr 1; apply Fin.ext; omega)
    | omega

theorem inverseScalarReg_core (r : TblR 25) (i : Fin 224) : inverseScalarReg r ≠ inverseCoreReg i := by
  intro he
  have hh := congrArg (fun k : Fin 264 => k.val) he
  cases r <;> simp only [inverseScalarReg,inverseCoreReg] at hh <;> omega

def inverseMasterCorePort : Fin 10 → Fin 224 := ![117,118,119,120,121,122,123,124,141,142]

def inverseMasterPort (i : Fin 10) : Fin 264 := inverseCoreReg (inverseMasterCorePort i)

theorem inverseMasterPort_injective : Function.Injective inverseMasterPort := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [inverseMasterPort,inverseCoreReg,inverseMasterCorePort]

theorem inverseScalarReg_master (i : Fin 10) (r : TblR 25) : inverseScalarReg r ≠ inverseMasterPort i := by
  exact inverseScalarReg_core r (inverseMasterCorePort i)

theorem inverseCallerReg_cover (i : Fin 264) :
    (∃ k, inverseCoreReg k = i) ∨ ∃ r, inverseScalarReg r = i := by
  by_cases hi : i.val < 224
  · exact Or.inl ⟨⟨i.val,hi⟩,Fin.ext rfl⟩
  · right
    by_cases hv : i.val < 249
    · exact ⟨.v ⟨i.val-224,by omega⟩,Fin.ext (by simp [inverseScalarReg]; omega)⟩
    by_cases h249 : i = 249
    · exact ⟨.wr,h249.symm⟩
    by_cases h250 : i = 250
    · exact ⟨.wn,h250.symm⟩
    by_cases h251 : i = 251
    · exact ⟨.acc,h251.symm⟩
    have h249' : i.val ≠ 249 := fun he => h249 (Fin.ext he)
    have h250' : i.val ≠ 250 := fun he => h250 (Fin.ext he)
    have h251' : i.val ≠ 251 := fun he => h251 (Fin.ext he)
    exact ⟨.z ⟨i.val-252,by omega⟩,Fin.ext (by simp [inverseScalarReg]; omega)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
