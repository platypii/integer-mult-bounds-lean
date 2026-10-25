module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScatterSchedule

/-! Natural equal-length cells form disjoint windows in their original ambient
line. Their publication gaps therefore fit one forward output sweep. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem naturalOrigins_disjoint (s t band L : ℕ) :
    (naturalOrigins s t band L).Pairwise (fun p q => p+L ≤ q) := by
  apply List.pairwise_map.mpr
  have hphases : (naturalLengthGroup s t band L).Pairwise (· < ·) :=
    List.Pairwise.filter _ List.pairwise_lt_range
  apply hphases.imp_of_mem
  intro p q hp _ hpq
  obtain ⟨_,hL,he⟩ := (mem_naturalLengthGroup s t band L p).mp hp
  have hmono : phaseLower s (t-s) (p+1) ≤ phaseLower s (t-s) q := by
    unfold phaseLower
    apply Nat.div_le_div_right
    exact Nat.sub_le_sub_right (Nat.sub_le_sub_right
      (Nat.add_le_add_right (Nat.mul_le_mul_left (2*s) (by omega : p+1 ≤ q)) (2*(t-s))) 1) s
  have hstop : naturalStop s t band p ≤ phaseLower s (t-s) (p+1) := by
    unfold naturalStop
    exact (Nat.sub_le _ _).trans (min_le_right _ _)
  unfold naturalLength naturalStart at he
  unfold naturalStart
  omega

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem naturalSymbolOrigins_disjoint (s t band L w : ℕ) :
    (naturalSymbolOrigins s t band L w).Pairwise (fun p q => p+L*w ≤ q) := by
  apply List.pairwise_map.mpr
  exact (naturalOrigins_disjoint s t band L).imp (fun h => by
    simpa only [Nat.add_mul] using Nat.mul_le_mul_right w h)

def naturalScatterGaps (s t band L w : ℕ) : List ℕ :=
  windowGaps (L*w) 0 (naturalSymbolOrigins s t band L w)

@[simp] theorem naturalScatterGaps_length (s t band L w : ℕ) :
    (naturalScatterGaps s t band L w).length = (naturalLengthGroup s t band L).length := by
  simp [naturalScatterGaps,naturalSymbolOrigins]

theorem naturalScatterGaps_fits {α : Type*} (s t band L w : ℕ) (E : List α)
    (hE : s*w ≤ E.length) : ScatterFits (L*w) E (naturalScatterGaps s t band L w) := by
  have hh := windowGaps_fits (L*w) 0 (naturalSymbolOrigins s t band L w) E
    (fun _ _ => Nat.zero_le _) (naturalSymbolOrigins_disjoint s t band L w)
    (fun p hp => (naturalSymbolOrigins_fit s t band L w p hp).trans hE)
  simpa [naturalScatterGaps] using hh

theorem naturalScatterGaps_volume (s t band L w : ℕ) :
    scatterVolume (L*w) (naturalScatterGaps s t band L w) ≤ s*w := by
  let E : List Unit := List.replicate (s*w) ()
  simpa [E] using scatterVolume_le (L*w) E (naturalScatterGaps s t band L w)
    (naturalScatterGaps_fits s t band L w E (by simp [E]))

theorem naturalScatterRows_window {α : Type*} (s t band L w : ℕ) (E X : List α)
    (hE : s*w ≤ E.length) (hX : (naturalLengthGroup s t band L).length*(L*w) ≤ X.length)
    (n : ℕ) (hn : n < (naturalSymbolOrigins s t band L w).length) :
    ((scatterRows (L*w) E X (naturalScatterGaps s t band L w)).drop
      (naturalSymbolOrigins s t band L w)[n]).take (L*w) = (X.drop (n*(L*w))).take (L*w) := by
  exact scatterRows_absolute (L*w) (naturalSymbolOrigins s t band L w) E X
    (naturalSymbolOrigins_disjoint s t band L w)
    (fun p hp => (naturalSymbolOrigins_fit s t band L w p hp).trans hE)
    (by simpa [naturalSymbolOrigins] using hX) n hn

/-- Physical word alignment survives scattering from packed rows to ambient coordinates. -/
theorem naturalScatterRows_word {α : Type*} {s : ℕ} [NeZero s] (t band L w : ℕ) (E X : List α)
    (hE : s*w ≤ E.length) (hX : (naturalLengthGroup s t band L).length*(L*w) ≤ X.length)
    (n : Fin (naturalLengthGroup s t band L).length) (i : Fin L) :
    ((scatterRows (L*w) E X (naturalScatterGaps s t band L w)).drop
      (((naturalGroupOrigin s t band L n).val+i.val)*w)).take w =
    (X.drop ((n.val*L+i.val)*w)).take w := by
  have hn : n.val < (naturalSymbolOrigins s t band L w).length := by
    simp [naturalSymbolOrigins]
  have horigin : (naturalSymbolOrigins s t band L w)[n.val] =
      (naturalGroupOrigin s t band L n).val*w := by
    rw [naturalGroupOrigin_val band L n]
    simp only [naturalSymbolOrigins,naturalOrigins,List.getElem_map,naturalGroupPhase,
      List.getD_eq_getElem _ _ n.isLt]
  have he := naturalScatterRows_window s t band L w E X hE hX n.val hn
  rw [horigin] at he
  have hcut : w ≤ L*w-i.val*w := by
    have hh := Nat.mul_le_mul_right w (Nat.succ_le_of_lt i.isLt)
    simp only [Nat.succ_mul] at hh
    omega
  have hh := congrArg (fun ys : List α => (ys.drop (i.val*w)).take w) he
  simpa only [List.drop_take,List.take_take,Nat.min_eq_left hcut,List.drop_drop,
    Nat.add_mul,Nat.mul_assoc] using hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
