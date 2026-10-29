module

public import IntegerMultBounds.NLogN.PhaseCellHaloBoundary

/-! # Spatial halo layers

These layers retain all phase cuts and shrink only at artificial endpoints.
Thus boundary rows of phase cells participate in the same locality proof as
interior rows. The matrix support theorem retains periodic aliases.
-/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open scoped BigOperators
open Finset PhaseCellDiscreteGeometry
variable {s t : ℕ} [NeZero s]

omit [NeZero s] in
/-- A nonzero matrix coefficient comes from a retained lattice offset. -/
theorem realMatrix_support (p u : ℕ) (i j : ZMod s)
    (h : realMatrix s t p u i j ≠ 0) :
    ∃ δ : ℤ, -(PhaseCellBand.width p u : ℤ) ≤ δ ∧
      δ ≤ PhaseCellBand.width p u ∧ i+(δ : ZMod s) = j := by
  by_contra hnone
  have hz (δ : ℤ) (hlo : -(PhaseCellBand.width p u : ℤ) ≤ δ)
      (hhi : δ ≤ PhaseCellBand.width p u) : i+(δ : ZMod s) ≠ j := by
    intro he
    exact hnone ⟨δ,hlo,hhi,he⟩
  apply h
  have hc := hz 0 (by omega) (by omega)
  have hp (n : ℕ) (hn : n ∈ range (PhaseCellBand.width p u)) :=
    hz ((n : ℤ)+1) (by have := mem_range.mp hn; omega) (by have := mem_range.mp hn; omega)
  have hm (n : ℕ) (hn : n ∈ range (PhaseCellBand.width p u)) :=
    hz (-((n : ℤ)+1)) (by have := mem_range.mp hn; omega) (by have := mem_range.mp hn; omega)
  simp only [realMatrix,matrix,PhaseCellRow.window,ite_eq_right hc]
  rw [sum_eq_zero (fun n hn => ite_eq_right (hp n hn)),
    sum_eq_zero (fun n hn => ite_eq_right (hm n hn))]
  norm_num

/-- Spatial layers do not remove neighborhoods of original phase cuts. -/
def haloLayer (s a b band n : ℕ) [NeZero s] : Finset (ZMod s) :=
  haloVertices s (a+n*band) (b-n*band)

theorem haloLayer_subset (a b band n : ℕ) :
    haloLayer s a b band n ⊆ haloVertices s a b := by
  intro i hi
  obtain ⟨ha,hb⟩ := (mem_haloVertices _ _ i).mp hi
  apply (mem_haloVertices a b i).mpr
  constructor <;> omega

/-- A band-sized shift from layer n+1 remains in layer n, with no new wrap. -/
theorem haloLayer_shift (a b band n : ℕ) (hb : b ≤ s) (i : ZMod s)
    (hi : i ∈ haloLayer s a b band (n+1)) (δ : ℤ)
    (hδ : -(band : ℤ) ≤ δ ∧ δ ≤ band) :
    i+(δ : ZMod s) ∈ haloLayer s a b band n := by
  obtain ⟨ha,hiB⟩ := (mem_haloVertices _ _ i).mp hi
  have hstep : (n+1)*band = n*band+band := by ring
  rw [hstep] at ha hiB
  have hjval : ((i+(δ : ZMod s)).val : ℤ) = (i.val : ℤ)+δ := by
    have he : i+(δ : ZMod s) = (((i.val : ℤ)+δ : ℤ) : ZMod s) := by simp
    rw [he,ZMod.val_intCast,Int.emod_eq_of_lt (by omega) (by omega)]
  apply (mem_haloVertices _ _ _).mpr
  constructor <;> omega

/-- Rotate only the coordinate chart used to describe a halo, not its matrix. -/
def cyclicHaloLayer (origin : ZMod s) (a b band n : ℕ) : Finset (ZMod s) :=
  univ.filter (fun i => i-origin ∈ haloLayer s a b band n)

@[simp] theorem mem_cyclicHaloLayer (origin i : ZMod s) (a b band n : ℕ) :
    i ∈ cyclicHaloLayer origin a b band n ↔ i-origin ∈ haloLayer s a b band n := by
  simp [cyclicHaloLayer]

theorem cyclicHaloLayer_subset (origin : ZMod s) (a b band n : ℕ) :
    cyclicHaloLayer origin a b band n ⊆ cyclicHaloLayer origin a b band 0 := by
  intro i hi
  rw [mem_cyclicHaloLayer] at hi ⊢
  simpa only [haloLayer,zero_mul,add_zero, Nat.sub_zero] using
    haloLayer_subset a b band n hi

theorem cyclicHaloLayer_shift (origin : ZMod s) (a b band n : ℕ) (hb : b ≤ s)
    (i : ZMod s) (hi : i ∈ cyclicHaloLayer origin a b band (n+1)) (δ : ℤ)
    (hδ : -(band : ℤ) ≤ δ ∧ δ ≤ band) :
    i+(δ : ZMod s) ∈ cyclicHaloLayer origin a b band n := by
  rw [mem_cyclicHaloLayer] at hi ⊢
  have h := haloLayer_shift a b band n hb (i-origin) hi δ hδ
  simpa only [sub_add_eq_add_sub] using h

end IntegerMultBounds.NLogN.PhaseCellMatrix
