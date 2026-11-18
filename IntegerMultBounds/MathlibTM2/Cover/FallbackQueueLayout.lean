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

end IntegerMultBounds.MathlibTM2.Cover.Fallback.QueueLayout
