module

public import IntegerMultBounds.MathlibTM2.Routing.RectangularHaloCoordinates
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Coordinate invariant for persistent tensor halos. Each axis is extended
once; previously retained axes keep their own local width and source projection. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.RetainedHaloTensor
open RectangularHaloCoordinates
open scoped BigOperators
variable {ι E : Type} [DecidableEq ι]

structure Axis where
  N : ℕ
  L : ℕ
  H : ℕ
  N_pos : 0 < N
  L_pos : 0 < L

def sourcePair (a : Axis) (kt : ℕ × ℕ) : ℕ × ℕ :=
  let j := sourceIndex a.N a.L a.H kt.1 kt.2
  (j/a.L,j%a.L)

theorem sourcePair_decode (a : Axis) (kt : ℕ × ℕ) :
    (sourcePair a kt).1*a.L+(sourcePair a kt).2 = sourceIndex a.N a.L a.H kt.1 kt.2 := by
  have hh := Nat.mod_add_div (sourceIndex a.N a.L a.H kt.1 kt.2) a.L
  simpa only [sourcePair,Nat.mul_comm,Nat.add_comm] using hh

theorem sourcePair_bounds (a : Axis) (kt : ℕ × ℕ) :
    (sourcePair a kt).1 < a.N ∧ (sourcePair a kt).2 < a.L := by
  have hh : sourceIndex a.N a.L a.H kt.1 kt.2 < a.N*a.L :=
    Nat.mod_lt _ (Nat.mul_pos a.N_pos a.L_pos)
  exact ⟨(Nat.div_lt_iff_lt_mul a.L_pos).mpr hh,Nat.mod_lt _ a.L_pos⟩

def localLength (axis : ι → Axis) (retained : Finset ι) (i : ι) : ℕ :=
  if i ∈ retained then (axis i).L+2*(axis i).H else (axis i).L

def Valid (axis : ι → Axis) (retained : Finset ι) (coords : ι → ℕ × ℕ) : Prop :=
  ∀ i, (coords i).1 < (axis i).N ∧ (coords i).2 < localLength axis retained i

def project (axis : ι → Axis) (retained : Finset ι) (coords : ι → ℕ × ℕ) : ι → ℕ :=
  fun i => if i ∈ retained then sourceIndex (axis i).N (axis i).L (axis i).H (coords i).1 (coords i).2
    else (coords i).1*(axis i).L+(coords i).2

def updateAxis (axis : ι → Axis) (i : ι) (coords : ι → ℕ × ℕ) : ι → ℕ × ℕ :=
  Function.update coords i (sourcePair (axis i) (coords i))

theorem updateAxis_other (axis : ι → Axis) (i j : ι) (hji : j ≠ i) (coords : ι → ℕ × ℕ) :
    updateAxis axis i coords j = coords j := Function.update_of_ne hji _ _

theorem updateAxis_update (axis : ι → Axis) (i : ι) (coords : ι → ℕ × ℕ) (kt : ℕ × ℕ) :
    updateAxis axis i (Function.update coords i kt) = Function.update coords i (sourcePair (axis i) kt) := by
  funext j
  by_cases hji : j = i
  · subst j; simp [updateAxis]
  · simp [updateAxis,hji]

theorem project_insert (axis : ι → Axis) (retained : Finset ι) (i : ι) (hi : i ∉ retained)
    (coords : ι → ℕ × ℕ) :
    project axis (insert i retained) coords = project axis retained (updateAxis axis i coords) := by
  funext j
  by_cases hji : j = i
  · subst j
    simpa [project,updateAxis,hi] using (sourcePair_decode (axis i) (coords i)).symm
  · simp [project,updateAxis,hji]

theorem updateAxis_valid (axis : ι → Axis) (retained : Finset ι) (i : ι) (hi : i ∉ retained)
    (coords : ι → ℕ × ℕ) (hc : Valid axis (insert i retained) coords) :
    Valid axis retained (updateAxis axis i coords) := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa [updateAxis,localLength,hi] using sourcePair_bounds (axis i) (coords i)
  · simpa [updateAxis,localLength,hji] using hc j

theorem project_bounds (axis : ι → Axis) (retained : Finset ι) (coords : ι → ℕ × ℕ)
    (hc : Valid axis retained coords) (i : ι) : project axis retained coords i < (axis i).N*(axis i).L := by
  by_cases hi : i ∈ retained
  · simpa [project,hi,sourceIndex] using
      Nat.mod_lt ((axis i).N*(axis i).L+((coords i).1*(axis i).L+(coords i).2)-(axis i).H)
        (Nat.mul_pos (axis i).N_pos (axis i).L_pos)
  · have hh := hc i
    simp only [localLength,ite_eq_right hi] at hh
    have hm := Nat.mul_le_mul_right (axis i).L (show (coords i).1+1 ≤ (axis i).N by omega)
    simp only [Nat.add_mul,Nat.one_mul] at hm
    simp only [project,ite_eq_right hi]
    omega

def pullback (axis : ι → Axis) (retained : Finset ι) (f : (ι → ℕ) → E) (coords : ι → ℕ × ℕ) : E :=
  f (project axis retained coords)

theorem pullback_insert (axis : ι → Axis) (retained : Finset ι) (i : ι) (hi : i ∉ retained)
    (f : (ι → ℕ) → E) (coords : ι → ℕ × ℕ) :
    pullback axis (insert i retained) f coords = pullback axis retained f (updateAxis axis i coords) := by
  unfold pullback
  rw [project_insert axis retained i hi]

theorem updateAxis_commute (axis : ι → Axis) (i j : ι) (hij : i ≠ j) (coords : ι → ℕ × ℕ) :
    updateAxis axis i (updateAxis axis j coords) = updateAxis axis j (updateAxis axis i coords) := by
  simp only [updateAxis,Function.update_of_ne hij,Function.update_of_ne hij.symm]
  exact (Function.update_comm hij _ _ _).symm

section Volume
variable [Fintype ι]

def volume (axis : ι → Axis) (retained : Finset ι) : ℕ :=
  ∏ i, (axis i).N*localLength axis retained i

theorem volume_insert_mul (axis : ι → Axis) (retained : Finset ι) (i : ι) (hi : i ∉ retained) :
    volume axis (insert i retained)*(axis i).L = volume axis retained*((axis i).L+2*(axis i).H) := by
  have hrest : (∏ j ∈ Finset.univ.erase i, (axis j).N*localLength axis (insert i retained) j) =
      ∏ j ∈ Finset.univ.erase i, (axis j).N*localLength axis retained j := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    simp [localLength,hji]
  have hnew := Finset.mul_prod_erase Finset.univ (fun j => (axis j).N*localLength axis (insert i retained) j)
    (Finset.mem_univ i)
  have hold := Finset.mul_prod_erase Finset.univ (fun j => (axis j).N*localLength axis retained j)
    (Finset.mem_univ i)
  unfold volume
  rw [←hnew,←hold,hrest]
  simp only [localLength,Finset.mem_insert_self,ite_true,ite_eq_right hi]
  ring

end Volume
end IntegerMultBounds.MathlibTM2.Routing.RetainedHaloTensor
