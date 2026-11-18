module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackDirectoryScan

/-! Shared registers for the directory reader, radix converter, and physical scan. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.QueueLayout
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Node LabelTraversal
variable {T : ℕ}

/-- Place a register block at a fixed offset within the joint workspace. -/
def block {n size : ℕ} (offset : ℕ) (fits : offset+n ≤ size) (host : Fin size ↪ Fin T) : Fin n ↪ Fin T :=
  (⟨fun i => ⟨offset+i.val,by have := i.isLt; omega⟩,
    fun i j h => Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))⟩ : Fin n ↪ Fin size).trans host

theorem block_ne {n m size : ℕ} {a b : ℕ} (ha : a+n ≤ size) (hb : b+m ≤ size)
    (host : Fin size ↪ Fin T) (apart : a+n ≤ b) (i : Fin n) (j : Fin m) :
    block a ha host i ≠ block b hb host j := by
  intro h
  have eq := congrArg Fin.val (host.injective h)
  change a+i.val = b+j.val at eq
  have := i.isLt
  omega

/-- The archive port may already be assigned by the signed pass. All other
ports are addressed through a separate workspace embedding. -/
def scanPorts (work : Fin 16 ↪ Fin T) (archive : Fin T) (apart : ∀ i, work i ≠ archive) : Fin 6 ↪ Fin T :=
  ⟨![work 12,work 1,work 2,work 4,archive,work 13],by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [Matrix.cons_val,work.injective.eq_iff]⟩

/-- The reader uses the freshly packed label in slot 10 and the retained projector in slot 16.
Slot 17 supplies one. The zero, width, and scratch tapes come from directory conversion. -/
def formulaInputs : Fin 10 ↪ Fin 18 := ⟨![0,8,10,3,4,5,6,16,9,17],by decide⟩

def directoryWork : Fin 16 ↪ Fin 18 := Fin.castLEEmb (by decide)

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
