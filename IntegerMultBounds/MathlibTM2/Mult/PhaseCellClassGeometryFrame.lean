module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedClassGeometryHeaders

/-! Geometry initialization changes only four numerical-bank ports. All caller
metadata, private workspaces and the supplier source have structural frame rules. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
variable {T A : ℕ}

theorem loadedClassGeometry_external (bank : ComputedClassBank → Fin T) (src : Fin 4 → Fin T)
    (S : Stacks T A) (k : Fin T) (hoff : ∀ i, k ≠ bank i) :
    (loadedClassGeometry bank src S).R k = S.R k := by
  apply copyWordHeadersR_off
  intro r hr
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
  exact (hoff (.geometry p.2)).symm

theorem loadedClassGeometry_bank_off (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
    (src : Fin 4 → Fin T) (S : Stacks T A) (i : ComputedClassBank)
    (hi : i ∉ [.geometry 32,.geometry 33,.geometry 34,.geometry 35]) :
    (loadedClassGeometry bank src S).R (bank i) = S.R (bank i) := by
  apply copyWordHeadersR_off
  intro r hr
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
  intro he
  have hi' : i = .geometry p.2 := (hinj he).symm
  apply hi
  rw [hi']
  simp only [classGeometryAssignments,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> decide

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
