module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackDirectoryScan

/-! Shared registers for the directory reader, radix converter, and physical scan. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.QueueLayout
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Node LabelTraversal
variable {T : ℕ}

/-- The archive port may already be assigned by the signed pass. All other
ports are addressed through a separate workspace embedding. -/
def scanPorts (work : Fin 16 ↪ Fin T) (archive : Fin T) (apart : ∀ i, work i ≠ archive) : Fin 6 ↪ Fin T :=
  ⟨![work 12,work 1,work 2,work 4,archive,work 13],by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [Matrix.cons_val,work.injective.eq_iff]⟩

def readPorts : Fin 7 ↪ Fin 16 := Fin.castLEEmb (by decide)
def digitPorts : Fin 6 ↪ Fin 16 := ⟨![3,11,7,14,8,15],by decide⟩

/-- Reuse the reciprocal, modulus, and scratch registers in the normalization pass.
The conjugated matrix is accumulated in slot 13, clear of the determinant in slot 14. -/
def normalizationPorts : Fin 14 ↪ Fin 16 := ⟨![0,1,4,13,2,3,5,6,7,8,9,10,11,12],by decide⟩

/-- Thirteen arithmetic registers serve all residual entries. The other four
ports select the identity coefficient, row weight, column weight, and archive. -/
def residualSlots : Fin 17 ↪ Fin 16 ⊕ Fin 4 :=
  ⟨![.inr 0,.inl 1,.inl 4,.inl 3,.inl 2,.inl 5,.inl 6,.inl 7,.inl 8,
     .inl 9,.inl 10,.inl 11,.inl 12,.inl 13,.inr 1,.inr 2,.inr 3],by decide⟩

def residualPorts (bank : Fin 16 ↪ Fin T) (coeff : Fin 4 ↪ Fin T)
    (apart : ∀ i j, bank i ≠ coeff j) : Fin 17 ↪ Fin T :=
  residualSlots.trans ⟨Sum.elim bank coeff,by
    intro x y h
    cases x <;> cases y
    · exact congrArg Sum.inl (bank.injective h)
    · exact False.elim (apart _ _ h)
    · exact False.elim (apart _ _ h.symm)
    · exact congrArg Sum.inr (coeff.injective h)⟩

theorem residualScratch (k : Fin 17) (hk : k = 1 ∨ 3 ≤ k ∧ k ≤ 12) :
    ∃ i : Fin 16, i ≠ 4 ∧ i < 13 ∧ residualSlots k = .inl i := by
  revert k
  decide

end IntegerMultBounds.MathlibTM2.Cover.Fallback.QueueLayout
