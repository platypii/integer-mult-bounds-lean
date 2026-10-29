module

public import IntegerMultBounds.NLogN.PhaseCellCoreWindows

/-! # Ordered groups for one-sweep halo exposure

Group only the fitting interval halos by length. Full-line fallbacks have a
separate shared descriptor and must not restart this ordered sweep. Geometry
keys here describe movement only; they do not assert numerical setup reuse.
-/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

def coreGatherIndices (s width radius L : ℕ) : List ℕ :=
  (coreIndices s width).filter (fun k => decide
    (radius ≤ coreStart width k ∧ coreStart width k+coreLength s width k+radius ≤ s ∧
      coreLength s width k+2*radius = L))

def coreGatherOrigins (s width radius L wordWidth : ℕ) : List ℕ :=
  (coreGatherIndices s width radius L).map (fun k => (coreStart width k-radius)*wordWidth)

theorem coreGatherIndices_spec (s width radius L k : ℕ)
    (hk : k ∈ coreGatherIndices s width radius L) :
    radius ≤ coreStart width k ∧ coreStart width k+coreLength s width k+radius ≤ s ∧
      coreLength s width k+2*radius = L := by
  simp only [coreGatherIndices,List.mem_filter,decide_eq_true_eq] at hk
  exact hk.2

theorem coreGatherOrigins_fit (s width radius L wordWidth : ℕ) :
    ∀ a ∈ coreGatherOrigins s width radius L wordWidth, a+L*wordWidth ≤ s*wordWidth := by
  intro a ha
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hl,hr,he⟩ := coreGatherIndices_spec s width radius L k hk
  have hfit : coreStart width k-radius+L ≤ s := by omega
  simpa only [Nat.add_mul] using Nat.mul_le_mul_right wordWidth hfit

theorem coreGatherOrigins_ordered (s width radius L wordWidth : ℕ) :
    (coreGatherOrigins s width radius L wordWidth).Pairwise (· ≤ ·) := by
  rw [coreGatherOrigins,List.pairwise_map]
  have h : (coreGatherIndices s width radius L).Pairwise (· < ·) :=
    (List.pairwise_lt_range).filter _
  apply h.imp
  intro i j hij
  apply Nat.mul_le_mul_right
  apply Nat.sub_le_sub_right
  exact Nat.mul_le_mul_right width hij.le

/-- Scheduled cores begin strictly inside the ambient line. -/
theorem coreIndex_start_lt (s width k : ℕ) (hw : 0 < width)
    (hk : k ∈ coreIndices s width) : coreStart width k < s := by
  have hlt : k < (s+width-1)/width := List.mem_range.mp hk
  have hm := Nat.mul_le_mul_right width hlt
  simp only [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul] at hm
  have hd := Nat.div_mul_le_self (s+width-1) width
  dsimp only [coreStart]
  omega

/-- Only the final clipped core can have a length different from width. -/
theorem coreLength_cases (s width k : ℕ) (hw : 0 < width)
    (hk : k ∈ coreIndices s width) :
    coreLength s width k = width ∨ coreLength s width k = s%width := by
  have hs := coreIndex_start_lt s width k hw hk
  by_cases hfull : width ≤ s-coreStart width k
  · exact Or.inl (min_eq_left hfull)
  · right
    have hlen : coreLength s width k = s-k*width := min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge hfull))
    have hlo : k ≤ s/width := (Nat.le_div_iff_mul_le hw).mpr hs.le
    have hhi : s/width < k+1 := (Nat.div_lt_iff_lt_mul hw).mpr (by
      dsimp only [coreStart] at hs hfull
      rw [Nat.add_mul,Nat.one_mul]
      omega)
    have he : s/width = k := by omega
    have hd := Nat.div_add_mod s width
    rw [he,Nat.mul_comm width] at hd
    omega

/-- Movement uses at most two length classes. Equality of these keys is not a
claim that the phase-dependent numerical setup pages can be shared. -/
def coreGatherLengths (s width radius : ℕ) : List ℕ :=
  [width+2*radius,s%width+2*radius].dedup

theorem coreGatherLengths_nodup (s width radius : ℕ) :
    (coreGatherLengths s width radius).Nodup := List.nodup_dedup _

theorem coreGatherLengths_length (s width radius : ℕ) :
    (coreGatherLengths s width radius).length ≤ 2 := by
  exact List.Sublist.length_le (List.dedup_sublist [width+2*radius,s%width+2*radius])

theorem coreGatherLengths_cover (s width radius L k : ℕ) (hw : 0 < width)
    (hk : k ∈ coreGatherIndices s width radius L) : L ∈ coreGatherLengths s width radius := by
  have hs := coreGatherIndices_spec s width radius L k hk
  have hk' : k ∈ coreIndices s width := (List.mem_filter.mp hk).1
  rcases coreLength_cases s width k hw hk' with he | he
  · simp only [he] at hs
    simp [coreGatherLengths,← hs.2.2]
  · simp only [he] at hs
    simp [coreGatherLengths,← hs.2.2]

/-- Every fitting scheduled core appears in a generated movement group. -/
theorem coreGatherIndices_cover (s width radius k : ℕ) (hw : 0 < width)
    (hk : k ∈ coreIndices s width)
    (hfit : radius ≤ coreStart width k ∧ coreStart width k+coreLength s width k+radius ≤ s) :
    ∃ L ∈ coreGatherLengths s width radius, k ∈ coreGatherIndices s width radius L := by
  have hm : k ∈ coreGatherIndices s width radius (coreLength s width k+2*radius) := by
    simp only [coreGatherIndices,List.mem_filter,decide_eq_true_eq]
    exact ⟨hk,hfit.1,hfit.2,trivial⟩
  exact ⟨_,coreGatherLengths_cover s width radius _ k hw hm,hm⟩

/-- A scheduled core is never processed by two distinct movement lengths. -/
theorem coreGatherIndices_unique (s width radius L M k : ℕ)
    (hL : k ∈ coreGatherIndices s width radius L)
    (hM : k ∈ coreGatherIndices s width radius M) : L = M :=
  (coreGatherIndices_spec s width radius L k hL).2.2.symm.trans
    (coreGatherIndices_spec s width radius M k hM).2.2

/-- Source traversal in the existing gather machine is paid at most twice. -/
theorem coreGather_traversal_bound (s width radius wordWidth : ℕ) :
    ((coreGatherLengths s width radius).map (fun _ => 12*s*wordWidth)).sum ≤ 24*s*wordWidth := by
  have h := Nat.mul_le_mul_right (12*s*wordWidth) (coreGatherLengths_length s width radius)
  have he : 2*(12*s*wordWidth) = 24*s*wordWidth := by ring
  rw [he] at h
  simpa using h

end IntegerMultBounds.NLogN.PhaseCellMatrix
