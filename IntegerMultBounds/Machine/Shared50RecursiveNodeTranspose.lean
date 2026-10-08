import IntegerMultBounds.Machine.Shared50RecursiveNodeSemantics

/-! The cyclic proof covers every original row, not merely a supplied subset.
The final word interchanges H/D at every seven-factor address. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveNodeTranspose
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open Shared50RecursiveNodeRows
variable {c : ℕ} {v : Descriptor}

def swapAddress (a : RecursiveInterchangeScaling.Address v) : RecursiveInterchangeScaling.Address v :=
  {a with h := a.d,d := a.h}

theorem transpose_all {α : Type*} (hc : 0 < c) (hd : c ∣ v.rows)
    (x : Fin (volume prime v) → α) (a : RecursiveInterchangeScaling.Address v) :
    transpose hd x (RecursiveInterchangeScaling.index (swapAddress a)) =
      x (RecursiveInterchangeScaling.index a) := by
  let g : Fin (v.rows/c) := ⟨a.row.val/c,Nat.div_lt_div_of_lt_of_dvd hd a.row.isLt⟩
  let j : Fin c := ⟨a.row.val%c,Nat.mod_lt _ hc⟩
  have hr : (⟨c*g.val+j.val,RecursiveInterchangeLayout.cyclic_row_lt c v g.val j.val g.isLt j.isLt hd⟩ : Fin v.rows) = a.row := by
    apply Fin.ext
    exact Nat.div_add_mod a.row.val c
  have ha : cyclicAddress hd a.beforeRows g j a.before a.h a.middle a.d a.after = a := by
    unfold cyclicAddress
    rw [hr]
  have hs : cyclicAddress hd a.beforeRows g j a.before a.d a.middle a.h a.after = swapAddress a := by
    unfold cyclicAddress swapAddress
    rw [hr]
  have ht := transpose_address hd x a.beforeRows g j a.before a.h a.middle a.d a.after
  rw [ha,hs] at ht
  exact ht

/-- Swapping complete field vectors packs to precisely the same physical H/D swap. -/
theorem packed_swap {b : ℕ} (hw : v.width=125000*b)
    (a : RecursiveScalarCoordinates.Address 125000 b v) :
    RecursiveScalarCoordinates.packed hw {a with h := a.d,d := a.h} =
      swapAddress (RecursiveScalarCoordinates.packed hw a) := rfl

theorem transpose_fields_all {α : Type*} {b : ℕ} (hw : v.width=125000*b)
    (hc : 0 < c) (hd : c ∣ v.rows) (x : Fin (volume prime v) → α)
    (a : RecursiveScalarCoordinates.Address 125000 b v) :
    transpose hd x (RecursiveScalarCoordinates.index hw {a with h := a.d,d := a.h}) =
      x (RecursiveScalarCoordinates.index hw a) := by
  simpa only [RecursiveScalarCoordinates.index,packed_swap] using
    transpose_all hc hd x (RecursiveScalarCoordinates.packed hw a)

end
end IntegerMultBounds.Machine.Shared50RecursiveNodeTranspose
