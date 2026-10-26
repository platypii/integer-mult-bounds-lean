module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScatterSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloGatherSchedule

/-! Clipped equal-length cells form disjoint windows in their original ambient
line. Their publication gaps therefore fit one forward output sweep. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem haloOrigins_disjoint (s t band a b L : ℕ) :
    (haloOrigins s t band a b L).Pairwise (fun p q => p+L ≤ q) := by
  apply List.pairwise_map.mpr
  have hphases : (haloLengthGroup s t band a b L).Pairwise (· < ·) :=
    List.Pairwise.filter _ List.pairwise_lt_range
  apply hphases.imp_of_mem
  intro p q hp _ hpq
  obtain ⟨_,hL,he⟩ := (mem_haloLengthGroup s t band a b L p).mp hp
  have hstop := haloCells_ordered s t band a b p q hpq
  unfold haloLength at he
  omega

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem haloSymbolOrigins_disjoint (s t band a b L w : ℕ) :
    (haloSymbolOrigins s t band a b L w).Pairwise (fun p q => p+L*w ≤ q) := by
  apply List.pairwise_map.mpr
  exact (haloOrigins_disjoint s t band a b L).imp (fun h => by
    simpa only [Nat.add_mul] using Nat.mul_le_mul_right w h)

def haloScatterGaps (s t band a b L w : ℕ) : List ℕ :=
  windowGaps (L*w) 0 (haloSymbolOrigins s t band a b L w)

@[simp] theorem haloScatterGaps_length (s t band a b L w : ℕ) :
    (haloScatterGaps s t band a b L w).length = (haloLengthGroup s t band a b L).length := by
  simp [haloScatterGaps,haloSymbolOrigins]

theorem haloScatterGaps_fits {α : Type*} (s t band a b L w : ℕ) (E : List α)
    (hE : s*w ≤ E.length) : ScatterFits (L*w) E (haloScatterGaps s t band a b L w) := by
  have hh := windowGaps_fits (L*w) 0 (haloSymbolOrigins s t band a b L w) E
    (fun _ _ => Nat.zero_le _) (haloSymbolOrigins_disjoint s t band a b L w)
    (fun p hp => (haloSymbolOrigins_fit s t band a b L w p hp).trans hE)
  simpa [haloScatterGaps] using hh

theorem haloScatterGaps_volume (s t band a b L w : ℕ) :
    scatterVolume (L*w) (haloScatterGaps s t band a b L w) ≤ s*w := by
  let E : List Unit := List.replicate (s*w) ()
  simpa [E] using scatterVolume_le (L*w) E (haloScatterGaps s t band a b L w)
    (haloScatterGaps_fits s t band a b L w E (by simp [E]))

theorem haloScatterRows_window {α : Type*} (s t band a b L w : ℕ) (E X : List α)
    (hE : s*w ≤ E.length) (hX : (haloLengthGroup s t band a b L).length*(L*w) ≤ X.length)
    (n : ℕ) (hn : n < (haloSymbolOrigins s t band a b L w).length) :
    ((scatterRows (L*w) E X (haloScatterGaps s t band a b L w)).drop
      (haloSymbolOrigins s t band a b L w)[n]).take (L*w) = (X.drop (n*(L*w))).take (L*w) := by
  exact scatterRows_absolute (L*w) (haloSymbolOrigins s t band a b L w) E X
    (haloSymbolOrigins_disjoint s t band a b L w)
    (fun p hp => (haloSymbolOrigins_fit s t band a b L w p hp).trans hE)
    (by simpa [haloSymbolOrigins] using hX) n hn

/-- Physical word alignment survives scattering from packed rows to ambient coordinates. -/
theorem haloScatterRows_word {α : Type*} {s : ℕ} [NeZero s] (t band a b L w : ℕ) (E X : List α)
    (hE : s*w ≤ E.length) (hX : (haloLengthGroup s t band a b L).length*(L*w) ≤ X.length)
    (n : Fin (haloLengthGroup s t band a b L).length) (i : Fin L) :
    ((scatterRows (L*w) E X (haloScatterGaps s t band a b L w)).drop
      (((haloGroupOrigin s t band a b L n).val+i.val)*w)).take w =
    (X.drop ((n.val*L+i.val)*w)).take w := by
  have hn : n.val < (haloSymbolOrigins s t band a b L w).length := by
    simp [haloSymbolOrigins]
  have horigin : (haloSymbolOrigins s t band a b L w)[n.val] =
      (haloGroupOrigin s t band a b L n).val*w := by
    rw [haloGroupOrigin_val band a b L n]
    simp only [haloSymbolOrigins,haloOrigins,List.getElem_map,haloGroupPhase,
      List.getD_eq_getElem _ _ n.isLt]
  have he := haloScatterRows_window s t band a b L w E X hE hX n.val hn
  rw [horigin] at he
  have hcut : w ≤ L*w-i.val*w := by
    have hh := Nat.mul_le_mul_right w (Nat.succ_le_of_lt i.isLt)
    simp only [Nat.succ_mul] at hh
    omega
  have hh := congrArg (fun ys : List α => (ys.drop (i.val*w)).take w) he
  simpa only [List.drop_take,List.take_take,Nat.min_eq_left hcut,List.drop_drop,
    Nat.add_mul,Nat.mul_assoc] using hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
