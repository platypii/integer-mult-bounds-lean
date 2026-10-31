module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedJob
public import IntegerMultBounds.NLogN.PhaseCellCoreGather

/-! A nonempty proper-core class reuses its jobs' common scalar width for the
origin controller. No additional width bank or per-origin sizing premise is needed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedNormalizedJob
open IntegerMultBounds IntegerMultBounds.NLogN.PhaseCellMatrix
variable {A s : ℕ} [NeZero s]

theorem coreWidth_lt (r : PackedNormalizedJob A s) (hk : r.k ∈ coreIndices s r.coreWidth) :
    r.coreWidth < s := by
  have hstart := coreStart_lt_of_mem hk
  by_contra hwidth
  have hkzero : r.k = 0 := by
    by_contra hzero
    have hm := Nat.mul_le_mul_right r.coreWidth (show 1 ≤ r.k by omega)
    simp only [Nat.one_mul] at hm
    dsimp only [coreStart] at hstart
    omega
  have hcore : coreLength s r.coreWidth r.k = s := by
    simp only [hkzero,coreLength,coreStart,Nat.zero_mul,Nat.sub_zero]
    exact Nat.min_eq_right (by omega)
  have hhalo := r.haloLength
  have hproper := r.haloLength_lt
  rw [hcore] at hhalo
  omega

theorem originController_fits (r : PackedNormalizedJob A s) (hk : r.k ∈ coreIndices s r.coreWidth) :
    0 < r.coreWidth ∧ s+r.coreWidth+2*r.radius < 2^r.Bcore ∧
      r.b-r.a < 2^r.Bcore ∧ 0 < r.Bcore := by
  have hstart := coreStart_lt_of_mem hk
  have hwidth := r.coreWidth_lt hk
  have hradius : r.radius < s := lt_of_le_of_lt r.hleft hstart
  have hst := r.bounds.hst
  have hgeo := r.hgeometryRoom
  have hzero : 0 < r.coreWidth := by
    by_contra h
    have hz : r.coreWidth = 0 := by omega
    simp only [coreIndices,hz,Nat.div_zero,List.range_zero,List.not_mem_nil] at hk
  have hroom : s+r.coreWidth+2*r.radius < 2^r.Bcore := by nlinarith
  have hL := r.haloLength_lt.trans r.hsCore
  have hB : 0 < r.Bcore := by
    by_contra h
    have hz : r.Bcore = 0 := by omega
    have hs := r.hsCore
    simp only [hz,pow_zero] at hs
    have hspos := NeZero.pos s
    omega
  exact ⟨hzero,hroom,hL,hB⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedNormalizedJob
