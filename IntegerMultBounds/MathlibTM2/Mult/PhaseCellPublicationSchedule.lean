module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAdvanceSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalScatterSchedule

/-! The existing origin advances contain exactly the publication gaps:
retain the first origin and subtract a window from each later advance. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def publicationGaps (L : ℕ) : List ℕ → List ℕ
  | [] => []
  | d::ds => d::ds.map (·-L)

theorem windowGaps_trimAdvances (L cursor : ℕ) (ps : List ℕ) :
    windowGaps L (cursor+L) ps = (originAdvances 1 cursor ps).map (·-L) := by
  induction ps generalizing cursor with
  | nil => rfl
  | cons p ps ih => simp [windowGaps,originAdvances,ih,Nat.sub_sub]

theorem windowGaps_publicationGaps (L : ℕ) (ps : List ℕ) :
    windowGaps L 0 ps = publicationGaps L (originAdvances 1 0 ps) := by
  cases ps with
  | nil => rfl
  | cons p ps => simp [windowGaps,originAdvances,publicationGaps,windowGaps_trimAdvances]

theorem naturalPublicationGaps (s t band L w : ℕ) :
    publicationGaps (L*w) (originAdvances w 0 (naturalOrigins s t band L)) =
      naturalScatterGaps s t band L w := by
  rw [originAdvances_symbols]
  simpa only [Nat.zero_mul,naturalScatterGaps,naturalSymbolOrigins] using
    (windowGaps_publicationGaps (L*w) ((naturalOrigins s t band L).map (·*w))).symm

theorem originAdvances_lower (L w previous : ℕ) (origins : List ℕ)
    (hdisjoint : (previous::origins).Pairwise (fun p q => p+L ≤ q)) :
    ∀ d ∈ originAdvances w previous origins, L*w ≤ d := by
  induction origins generalizing previous with
  | nil => simp [originAdvances]
  | cons origin origins ih =>
    have ht := List.pairwise_cons.mp hdisjoint
    intro d hd
    simp only [originAdvances,List.mem_cons] at hd
    rcases hd with rfl | hd
    · apply Nat.mul_le_mul_right
      have hh := ht.1 origin (by simp)
      omega
    · exact ih origin ht.2 d hd

theorem gatherControls_append (A : ℕ) (ds es : List ℕ) :
    gatherControls A (ds++es) = gatherControls A ds++gatherControls A es := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [gatherControls,ih,List.append_assoc]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
