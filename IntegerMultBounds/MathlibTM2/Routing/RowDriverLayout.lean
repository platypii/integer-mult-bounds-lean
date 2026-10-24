module

public import IntegerMultBounds.MathlibTM2.Routing.FramedCoreLayout

/-! Seven fixed driver tapes outside the reusable router bank: row count,
count archive, width, unread input, transfer buffer, scratch and output archive.
The work stream remains inside the router bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

def rowDriverEmbed (N : ℕ) (j : Fin N) : Fin (N + 7) := Fin.castAdd 7 j

def rowDriverAux (N : ℕ) (i : Fin 7) : Fin (N + 7) := ⟨N + i.val, by omega⟩

theorem rowDriverEmbed_injective (N : ℕ) : Function.Injective (rowDriverEmbed N) := by
  intro i j h
  have hv := congrArg (fun x : Fin (N + 7) => x.val) h
  exact Fin.ext hv

theorem rowDriverAux_injective (N : ℕ) : Function.Injective (rowDriverAux N) := by
  intro i j h
  have hv := congrArg Fin.val h
  apply Fin.ext
  change N + i.val = N + j.val at hv
  omega

theorem rowDriverEmbed_aux (N : ℕ) (j : Fin N) (i : Fin 7) :
    rowDriverEmbed N j ≠ rowDriverAux N i := by
  intro h
  have hv := congrArg Fin.val h
  change j.val = N + i.val at hv
  have := j.isLt
  omega

/-- The actual register order required by the counted row-call theorem. -/
theorem rowDriver_registers_nodup (N : ℕ) (str : Fin N) :
    [rowDriverAux N 0, rowDriverAux N 1, rowDriverAux N 2, rowDriverAux N 3,
      rowDriverEmbed N str, rowDriverAux N 4, rowDriverAux N 5, rowDriverAux N 6].Nodup := by
  have haux (i : Fin 7) : rowDriverAux N i ≠ rowDriverEmbed N str :=
    (rowDriverEmbed_aux N str i).symm
  simp [List.nodup_cons, (rowDriverAux_injective N).eq_iff, rowDriverEmbed_aux, haux]

end IntegerMultBounds.MathlibTM2.Routing
