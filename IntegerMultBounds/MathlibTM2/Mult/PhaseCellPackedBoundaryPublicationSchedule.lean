module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryScatterData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationSchedule

/-! The existing advance-to-publication converter applies to packed offsets.
Its control volume is bounded by halo length, independently of its origin. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

/-- Retain ambient origin packets and start the scanner at the halo origin.
The resulting relative controls equal those from translated packets. -/
theorem originAdvances_translate (w a previous : ℕ) (ps : List ℕ)
    (hprevious : a ≤ previous) (hbefore : ∀ p ∈ ps, a ≤ p) :
    originAdvances w (previous-a) (ps.map (·-a)) = originAdvances w previous ps := by
  induction ps generalizing previous with
  | nil => rfl
  | cons p ps ih =>
    have hp := hbefore p (by simp)
    simp only [List.map_cons,originAdvances]
    rw [show p-a-(previous-a) = p-previous by omega,
      ih p hp (fun q hq => hbefore q (by simp [hq]))]

theorem packedBoundaryAdvances_from_ambient {s : ℕ} [NeZero s]
    (B : Finset (ZMod s)) (a L w : ℕ)
    (hB : ∀ i ∈ B, a ≤ i.val ∧ i.val < a+L) :
    originAdvances w a ((IntegerMultBounds.NLogN.PhaseCellMatrix.bOrder s B).map ZMod.val) =
      originAdvances w 0 (packedBoundaryOrigins B a) := by
  have hbefore : ∀ p ∈ (IntegerMultBounds.NLogN.PhaseCellMatrix.bOrder s B).map ZMod.val,
      a ≤ p := by
    intro p hp
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
    have hm : i ∈ B := by
      simpa only [← List.mem_toFinset,IntegerMultBounds.NLogN.PhaseCellMatrix.bOrder_toFinset] using hi
    exact (hB i hm).1
  have hh := originAdvances_translate w a a
    ((IntegerMultBounds.NLogN.PhaseCellMatrix.bOrder s B).map ZMod.val) le_rfl hbefore
  simpa only [Nat.sub_self,List.map_map,Function.comp_def,packedBoundaryOrigins] using hh.symm

theorem packedBoundaryPublicationGaps {s : ℕ} [NeZero s]
    (B : Finset (ZMod s)) (a w : ℕ) :
    publicationGaps w (originAdvances w 0 (packedBoundaryOrigins B a)) =
      packedBoundaryGaps B a w := by
  rw [originAdvances_symbols]
  simpa only [Nat.zero_mul,packedBoundaryGaps] using
    (windowGaps_publicationGaps w ((packedBoundaryOrigins B a).map (·*w))).symm

theorem packedBoundaryOriginAdvances_volume {s : ℕ} [NeZero s]
    (B : Finset (ZMod s)) (a L w : ℕ)
    (hB : ∀ i ∈ B, a ≤ i.val ∧ i.val < a+L) :
    (originAdvances w 0 (packedBoundaryOrigins B a)).sum ≤ L*w := by
  have ho : (0::packedBoundaryOrigins B a).Pairwise (· ≤ ·) :=
    List.pairwise_cons.mpr ⟨by simp,
      (packedBoundaryOrigins_disjoint B a L hB).imp (fun h => by omega)⟩
  simpa using originAdvances_sum_le w 0 L (packedBoundaryOrigins B a) ho (Nat.zero_le _)
    (fun p hp => (packedBoundaryOrigins_fit B a L hB p hp).trans' (Nat.le_succ _))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
