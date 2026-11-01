module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloClassPublicationWindows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreRead

/-! Canonical local windows and ambient geometry for the replica class loop. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

def haloSpanPublicationWindows (s t band origin span L : ℕ) (hL : 0 < L) : PublicationWindows span L where
  origins := haloPackedOffsets s t band origin (origin+span) L
  disjoint := haloPackedOffsets_disjoint s t band origin (origin+span) L
  fits := by simpa using haloPackedOffsets_fit s t band origin (origin+span) L
  count_le := by simpa [haloClassPublicationWindows] using (haloClassPublicationWindows s t band origin (origin+span) L hL).count_le

def haloReplicaClassOrigin {s : ℕ} (t band origin span L j : ℕ) : ZMod s :=
  (origin+(haloPackedOffsets s t band origin (origin+span) L).getD j 0 : ℕ)

theorem haloReplicaClassOrigin_eq_group {s : ℕ} (t band origin span L j : ℕ)
    (hj : j < (haloPackedOffsets s t band origin (origin+span) L).length) :
    haloReplicaClassOrigin (s := s) t band origin span L j =
      haloGroupOrigin s t band origin (origin+span) L j := by
  have hn : j < (haloLengthGroup s t band origin (origin+span) L).length := by simpa using hj
  have he := packedHaloGroupOrigin_eq (s := s) t band origin (origin+span) L j hn
  simpa only [haloReplicaClassOrigin,packedCellOrigin,List.getD_eq_getElem _ _ hj,
    List.getElem?_eq_getElem hj,Option.getD_some] using he

theorem haloReplicaClassOrigin_geometry {s t : ℕ} [NeZero s] (hst : s < t)
    (band origin span L : ℕ) (j : Fin (haloPackedOffsets s t band origin (origin+span) L).length) :
    let lo := haloReplicaClassOrigin (s := s) t band origin span L j
    let I := haloInterior s t band origin (origin+span)
    0 < L ∧ lo.val+L ≤ s ∧
      (∀ i < L, Interior s t band (lo+(i : ZMod s)) ∧ lo+(i : ZMod s) ∈ I) ∧
      (∀ i < L, cell s t (lo+(i : ZMod s)) = cell s t lo) ∧
      ∀ k ∈ I, cell s t k = cell s t lo → ∃ i < L, lo+(i : ZMod s) = k := by
  dsimp only
  rw [haloReplicaClassOrigin_eq_group _ _ _ _ _ _ j.isLt]
  exact haloGroup_solver_geometry hst band origin (origin+span) L ⟨j.val,by simpa using j.isLt⟩

theorem haloReplicaClassCore_bounds {s : ℕ} [NeZero s]
    (t band origin span L : ℕ) (hspan : origin+span ≤ s)
    (j : Fin (haloPackedOffsets s t band origin (origin+span) L).length)
    (k : ZMod s) (hk : k ∈ publishedCellCore (haloReplicaClassOrigin t band origin span L j) L) :
    origin ≤ k.val ∧ k.val < origin+span ∧
      (haloPackedOffsets s t band origin (origin+span) L)[j.val] ≤ k.val-origin ∧
      k.val-origin < (haloPackedOffsets s t band origin (origin+span) L)[j.val]+L := by
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
  have hiL := Finset.mem_range.mp hi
  have hfit := haloPackedOffsets_fit s t band origin (origin+span) L _ (List.getElem_mem j.isLt)
  simp only [Nat.add_sub_cancel_left] at hfit
  have he : haloReplicaClassOrigin (s := s) t band origin span L j+(i : ZMod s) =
      ((origin+(haloPackedOffsets s t band origin (origin+span) L)[j.val]+i : ℕ) : ZMod s) := by
    simp only [haloReplicaClassOrigin,List.getD_eq_getElem _ _ j.isLt,Nat.cast_add,add_assoc]
  have hsum : origin+(haloPackedOffsets s t band origin (origin+span) L)[j.val]+i < s := by omega
  rw [he,ZMod.val_cast_of_lt hsum]
  omega

theorem haloReplicaClassCore_avoids {s : ℕ} [NeZero s]
    (t band origin span K L : ℕ) (hspan : origin+span ≤ s) (hKL : K ≠ L)
    (j : Fin (haloPackedOffsets s t band origin (origin+span) K).length)
    (k : ZMod s) (hk : k ∈ publishedCellCore (haloReplicaClassOrigin t band origin span K j) K)
    (n : Fin (haloPackedOffsets s t band origin (origin+span) L).length) :
    k.val-origin+1 ≤ (haloPackedOffsets s t band origin (origin+span) L)[n.val] ∨
      (haloPackedOffsets s t band origin (origin+span) L)[n.val]+L ≤ k.val-origin := by
  have hb := haloReplicaClassCore_bounds t band origin span K hspan j k hk
  have hd := haloPackedOffsets_cross_disjoint s t band origin (origin+span) K L hKL
    _ (List.getElem_mem j.isLt) _ (List.getElem_mem n.isLt)
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
