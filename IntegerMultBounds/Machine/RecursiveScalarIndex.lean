import IntegerMultBounds.Machine.RecursiveScalarCoordinates

/-! Every serialized cell has original scalar coordinates, including all
spectator fields. No positivity hypothesis or restricted-address oracle. -/
namespace IntegerMultBounds.Machine.RecursiveScalarIndex
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
variable {m b : ℕ} {v : Descriptor}
local instance : NeZero (ActualAffineScaling.modulus b) := ⟨ne_of_gt (ActualAffineScaling.modulus_pos b)⟩

theorem scaling_surjective : Function.Surjective (RecursiveInterchangeScaling.index (v := v)) := by
  intro z
  obtain ⟨⟨p,e⟩,rfl⟩ := (finProdFinEquiv :
    Fin (v.beforeRows*v.rows*v.beforeH*prime^v.width*v.between*prime^v.width) × Fin v.afterD ≃ _).surjective z
  obtain ⟨⟨p,d⟩,rfl⟩ := (finProdFinEquiv :
    Fin (v.beforeRows*v.rows*v.beforeH*prime^v.width*v.between) × Fin (prime^v.width) ≃ _).surjective p
  obtain ⟨⟨p,c⟩,rfl⟩ := (finProdFinEquiv :
    Fin (v.beforeRows*v.rows*v.beforeH*prime^v.width) × Fin v.between ≃ _).surjective p
  obtain ⟨⟨p,h⟩,rfl⟩ := (finProdFinEquiv :
    Fin (v.beforeRows*v.rows*v.beforeH) × Fin (prime^v.width) ≃ _).surjective p
  obtain ⟨⟨p,before⟩,rfl⟩ := (finProdFinEquiv :
    Fin (v.beforeRows*v.rows) × Fin v.beforeH ≃ _).surjective p
  obtain ⟨⟨a,r⟩,rfl⟩ := (finProdFinEquiv : Fin v.beforeRows × Fin v.rows ≃ _).surjective p
  exact ⟨⟨a,r,before,h,c,d,e⟩,rfl⟩

theorem packed_surjective (hw : v.width=m*b) : Function.Surjective (RecursiveScalarCoordinates.packed hw) := by
  intro a
  have he : prime^v.width = (ActualAffineScaling.modulus b)^m := by
    rw [ActualAffineScaling.modulus,← pow_mul,hw,Nat.mul_comm b]
  let h := FlatCoordinateLayout.coordinates (Fin.cast he a.h)
  let d := FlatCoordinateLayout.coordinates (Fin.cast he a.d)
  refine ⟨⟨a.beforeRows,a.row,a.before,h,a.middle,d,a.after⟩,?_⟩
  unfold RecursiveScalarCoordinates.packed
  simp only [h,d,FlatCoordinateLayout.rank_coordinates]
  cases a
  rfl

theorem surjective (hw : v.width=m*b) : Function.Surjective (RecursiveScalarCoordinates.index hw) :=
  scaling_surjective.comp (packed_surjective hw)

end
end IntegerMultBounds.Machine.RecursiveScalarIndex
