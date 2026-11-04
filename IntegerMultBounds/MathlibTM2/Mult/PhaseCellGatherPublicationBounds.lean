module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationHeaderWords
public import IntegerMultBounds.NLogN.PhaseCellCoreGather
public import Mathlib.Data.Nat.Log

/-! The publication rectangle is smaller than its gathered halo rectangle.
Nonempty gather classes contain a positive owned core. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds IntegerMultBounds.NLogN.PhaseCellMatrix

theorem gatherPublicationShapeBounds (s width radius H W V b : ℕ)
    (hwidth : 0 < width) (hgroup : 0 < (coreGatherIndices s width radius H).length)
    (hpacket : 0 < H*W)
    (hbits : b+Nat.clog 2 (coreGatherIndices s width radius H).length < V)
    (hfit : (H*W)*2^(b+Nat.clog 2 (coreGatherIndices s width radius H).length) < 2^V)
    (hvolume : s*W < 2^V) :
    PublicationShapeBounds (Nat.clog 2 (coreGatherIndices s width radius H).length)
      b (H-2*radius) W V s (coreGatherIndices s width radius H).length := by
  obtain ⟨k,hk⟩ := List.exists_mem_of_length_pos hgroup
  have hmem : k ∈ coreIndices s width := (List.mem_filter.mp hk).1
  have hstart := coreStart_lt_of_mem hmem
  have hlen : 0 < coreLength s width k := by
    simp only [coreLength,lt_min_iff]
    omega
  have hhalo := (coreGatherIndices_spec s width radius H k hk).2.2
  have hcore : 0 < H-2*radius := by omega
  have hW : 0 < W := by
    by_contra hz
    have hh : W = 0 := by omega
    simp only [hh,Nat.mul_zero,lt_self_iff_false] at hpacket
  have hpower : 0 < 2^(b+Nat.clog 2 (coreGatherIndices s width radius H).length) := pow_pos (by decide) _
  have hrectangle : H*W ≤ (H*W)*2^(b+Nat.clog 2 (coreGatherIndices s width radius H).length) :=
    Nat.le_mul_of_pos_right _ hpower
  refine ⟨Nat.mul_pos hcore hW,?_,?_,Nat.le_pow_clog (by decide) _,?_,?_,hvolume⟩
  · simpa only [Nat.add_comm] using hbits
  · have hh := (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right W (Nat.sub_le H (2*radius)))).trans_lt hfit
    simpa only [Nat.add_comm] using hh
  · exact (Nat.le_mul_of_pos_left W (by omega : 0 < H)).trans_lt (hrectangle.trans_lt hfit)
  · exact (Nat.le_mul_of_pos_right s hW).trans_lt hvolume

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
