module

public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleCall
public import IntegerMultBounds.MathlibTM2.M6.BitIntervalOwners

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open RecursiveInterchangeLayout IntervalDescriptor
open Shared50ModularControl (prime)

theorem recordPayload_castInput {T m n : ℕ} (size : m = n) (slot : Fin T)
    (S : Stacks T prime) (word : Fin n → ZMod 2) (record : RecordPayload slot (fun _ => blank) 0 word S) :
    RecordPayload slot (fun _ => blank) 0 (fun k => word (k.cast size)) S := by
  subst n
  exact record

theorem parentReadOfPhysicalTranspose (i : Fin 9) (j : Fin 222) (a W : ℕ)
    (wide : Descriptor) (shape : wide = phaseIntervalChild ((idleInterval i j).1+1) ((idleInterval i j).2+1) a W 64)
    (cells : volume prime wide = (prime^a)^128*W) (word : Fin ((prime^a)^128*W) → ZMod 2)
    (y : Fin (volume prime wide) → ZMod 2)
    (same : y = Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) (fun k => word (k.cast cells))) :
    parentIntervalRead i j a W word (fun k => y (k.cast cells.symm)) := by
  subst wide y
  intro k
  rfl

/-- Return a scheduled directory result as a record in the parent's flat owner
order. The inherited child positions identify the transpose at every cell. -/
theorem scheduledIdleParentRecord {T : ℕ} (slot : Fin T) (F : Stacks T prime)
    (i : Fin 9) (j : Fin 222) (a W : ℕ) (child wide : Descriptor)
    (shape : wide = phaseIntervalChild ((idleInterval i j).1+1) ((idleInterval i j).2+1) a W 64)
    (cells : volume prime wide = (prime^a)^128*W)
    (position : Fin (volume prime child) ≃ Fin (volume prime wide))
    (coords : InheritedIntervalPositions child wide rfl position) (width : wide.width = child.width)
    (word : Fin ((prime^a)^128*W) → ZMod 2) (y : Fin (volume prime wide) → ZMod 2)
    (record : RecordPayload slot (fun _ => blank) 0 y F)
    (action : ∀ k, y (position k) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows)
      ((fun h => word (h.cast cells)) ∘ position) k) :
    ∃ changed, RecordPayload slot (fun _ => blank) 0 changed F ∧ parentIntervalRead i j a W word changed := by
  refine ⟨fun k => y (k.cast cells.symm),castPayload cells _ _ _ record,?_⟩
  exact parentReadOfPhysicalTranspose i j a W wide shape cells word y
    ((coords.transpose_iff width (fun h => word (h.cast cells)) y).1 action)

end IntegerMultBounds.MathlibTM2.M6.BitNode
