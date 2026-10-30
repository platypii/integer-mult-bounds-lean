module

public import IntegerMultBounds.NLogN.PhaseCellHaloLayers

/-! # Generated owned cores

Quotient indexing partitions the ambient line into consecutive cores. The last
core clips automatically. Halos may wrap, but publication retains this disjoint
ownership in the original ambient coordinate order.
-/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open Finset PhaseCellDiscreteGeometry
variable {s : ℕ} [NeZero s]

def coreStart (width k : ℕ) : ℕ := k*width

def coreLength (s width k : ℕ) : ℕ := min width (s-coreStart width k)

def coreIndices (s width : ℕ) : List ℕ := List.range ((s+width-1)/width)

def ownedCore (s width k : ℕ) [NeZero s] : Finset (ZMod s) :=
  haloVertices s (coreStart width k) (coreStart width k+coreLength s width k)

/-- Every scheduled core starts within the ambient line. Empty schedules need
no positivity assumption on the width. -/
theorem coreStart_lt_of_mem {s width k : ℕ} (hk : k ∈ coreIndices s width) :
    coreStart width k < s := by
  have hk' : k < (s+width-1)/width := List.mem_range.mp hk
  by_cases hw : width = 0
  · simp [hw] at hk'
  · have hm := Nat.mul_le_mul_right width (Nat.succ_le_of_lt hk')
    have hd := Nat.div_mul_le_self (s+width-1) width
    simp only [Nat.succ_mul] at hm
    dsimp only [coreStart]
    omega

/-- Membership is exactly quotient ownership, including the clipped last core. -/
theorem mem_ownedCore (width k : ℕ) (hw : 0 < width) (i : ZMod s) :
    i ∈ ownedCore s width k ↔ i.val/width = k := by
  rw [ownedCore,mem_haloVertices]
  have hi := i.val_lt
  have hdiv := Nat.div_add_mod i.val width
  rw [Nat.mul_comm width] at hdiv
  have hmod := Nat.mod_lt i.val hw
  dsimp only [coreStart,coreLength]
  constructor
  · intro h
    have hmin := min_le_left width (s-k*width)
    have hlo : k ≤ i.val/width := (Nat.le_div_iff_mul_le hw).mpr (by omega)
    have hhi : i.val/width < k+1 := (Nat.div_lt_iff_lt_mul hw).mpr (by
      rw [Nat.add_mul]
      omega)
    omega
  · intro h
    rw [h] at hdiv
    constructor
    · omega
    · have hstart : k*width ≤ i.val := by omega
      have htail : i.val-k*width < s-k*width := by omega
      have hrem : i.val-k*width < width := by omega
      have hmin := lt_min hrem htail
      omega

/-- The quotient owner is present in the computed finite schedule. -/
theorem coreOwner_mem (width : ℕ) (hw : 0 < width) (i : ZMod s) :
    i.val/width ∈ coreIndices s width := by
  rw [coreIndices,List.mem_range]
  apply (Nat.lt_div_iff_mul_lt hw).mpr
  have hi := i.val_lt
  have hdiv := Nat.div_add_mod i.val width
  rw [Nat.mul_comm width] at hdiv
  have hmod := Nat.mod_lt i.val hw
  omega

theorem ownedCore_cover (width : ℕ) (hw : 0 < width) (i : ZMod s) :
    ∃ k ∈ coreIndices s width, i ∈ ownedCore s width k :=
  ⟨i.val/width,coreOwner_mem width hw i,(mem_ownedCore width _ hw i).mpr rfl⟩

/-- Publication never has competing owners. -/
theorem ownedCore_disjoint (width k l : ℕ) (hw : 0 < width) (hkl : k ≠ l) :
    Disjoint (ownedCore s width k) (ownedCore s width l) := by
  apply disjoint_left.mpr
  intro i hi hj
  exact hkl (((mem_ownedCore width k hw i).mp hi).symm.trans
    ((mem_ownedCore width l hw i).mp hj))

/-- Halo origins are offset from their core by the required guard radius. -/
def coreHaloOrigin (s width k radius : ℕ) : ZMod s :=
  (coreStart width k : ZMod s)-(radius : ZMod s)

/-- A padded core lies in the selected cyclic locality layer. If padding would
fill the ambient line, the caller instead uses the full principal system. -/
theorem ownedCore_in_layer (width k band n : ℕ)
    (hfit : coreLength s width k+2*(n*band) ≤ s) (i : ZMod s)
    (hi : i ∈ ownedCore s width k) :
    i ∈ cyclicHaloLayer (coreHaloOrigin s width k (n*band)) 0
      (coreLength s width k+2*(n*band)) band n := by
  obtain ⟨hstart,hstop⟩ := (mem_haloVertices _ _ i).mp hi
  let offset := i.val-coreStart width k
  have hoff : offset < coreLength s width k := by dsimp [offset]; omega
  have he : i-coreHaloOrigin s width k (n*band) = ((offset+n*band : ℕ) : ZMod s) := by
    have hv : i = (i.val : ZMod s) := by simp
    rw [hv,coreHaloOrigin]
    have hcast : ((i.val-coreStart width k : ℕ) : ZMod s) =
        (i.val : ZMod s)-(coreStart width k : ZMod s) := Nat.cast_sub hstart
    simp only [offset,Nat.cast_add,hcast]
    ring
  have hlt : offset+n*band < s := by omega
  rw [mem_cyclicHaloLayer,he]
  apply (mem_haloVertices _ _ _).mpr
  rw [ZMod.val_cast_of_lt hlt]
  constructor <;> omega

/-- An interval halo fits the existing S3 descriptor ABI. Near the periodic
seam the full-line descriptor supplies the same principal-system semantics. -/
def coreHalo (s width k band n : ℕ) [NeZero s] : Finset (ZMod s) :=
  if n*band ≤ coreStart width k ∧
      coreStart width k+coreLength s width k+n*band ≤ s then
    haloVertices s (coreStart width k-n*band)
      (coreStart width k+coreLength s width k+n*band)
  else univ

/-- Padding places every owned coordinate at the requested interval depth. -/
theorem ownedCore_in_interval_layer (width k band n : ℕ)
    (hleft : n*band ≤ coreStart width k) (i : ZMod s)
    (hi : i ∈ ownedCore s width k) :
    i ∈ haloLayer s (coreStart width k-n*band)
      (coreStart width k+coreLength s width k+n*band) band n := by
  obtain ⟨ha,hb⟩ := (mem_haloVertices _ _ i).mp hi
  apply (mem_haloVertices _ _ _).mpr
  constructor <;> omega

theorem ownedCore_subset_halo (width k band n : ℕ) :
    ownedCore s width k ⊆ coreHalo s width k band n := by
  intro i hi
  unfold coreHalo
  split
  · rename_i hfit
    exact haloLayer_subset _ _ band n (ownedCore_in_interval_layer width k band n hfit.1 i hi)
  · exact mem_univ i

end IntegerMultBounds.NLogN.PhaseCellMatrix
