module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloGroups
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationWindows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloOriginPackets

/-! The actual generated halo class is a publication schedule in local coordinates. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

private theorem disjointWindows_count_le {span L : ℕ} (hL : 0 < L) (xs : List ℕ)
    (hdis : xs.Pairwise (fun p q => p+L ≤ q)) (hfit : ∀ p ∈ xs, p+L ≤ span)
    (base : ℕ) (hspan : base ≤ span) (hbase : ∀ p ∈ xs, base ≤ p) : xs.length+base ≤ span := by
  induction xs generalizing base with
  | nil => simpa using hspan
  | cons p xs ih =>
    obtain ⟨hp,hdis⟩ := List.pairwise_cons.mp hdis
    have hpfit := hfit p (by simp)
    have hpbase := hbase p (by simp)
    have htail := ih hdis (fun q hq => hfit q (List.mem_cons_of_mem _ hq)) (p+1)
      (by omega) (fun q hq => by have hh := hp q hq; omega)
    simp only [List.length_cons]
    omega

def haloClassPublicationWindows (s t band a b L : ℕ) (hL : 0 < L) : PublicationWindows (b-a) L where
  origins := haloPackedOffsets s t band a b L
  disjoint := haloPackedOffsets_disjoint s t band a b L
  fits := haloPackedOffsets_fit s t band a b L
  count_le := by
    simpa using disjointWindows_count_le hL (haloPackedOffsets s t band a b L)
      (haloPackedOffsets_disjoint s t band a b L) (haloPackedOffsets_fit s t band a b L)
      0 (Nat.zero_le _) (fun _ _ => Nat.zero_le _)

theorem haloClassPublicationWindows_ambient_packets {A s : ℕ} [NeZero s]
    (V t band a b L : ℕ) (hL : 0 < L) :
    let windows := haloClassPublicationWindows s t band a b L hL
    (List.range windows.origins.length).flatMap
      (fun j => binSyms (A := A) V ((a+windows.origins.getD j 0 : ℕ) : ZMod s).val) =
      haloOriginPackets A V s t band a b L := by
  dsimp only
  rw [haloOriginPackets_eq_rows]
  simp only [haloClassPublicationWindows,haloPackedOffsets_length]
  apply List.flatMap_congr
  intro j hj
  have hbound : j < (haloLengthGroup s t band a b L).length := by
    simpa only [List.mem_range,haloClassPublicationWindows,haloPackedOffsets_length] using hj
  have he := packedHaloGroupOrigin_eq (s := s) t band a b L j hbound
  have hj' : j < (haloPackedOffsets s t band a b L).length := by simpa using hbound
  simpa only [haloClassPublicationWindows,packedCellOrigin,List.getD_eq_getElem _ _ hj',
    List.getElem?_eq_getElem hj',Option.getD_some] using congrArg (fun z : ZMod s => binSyms (A := A) V z.val) he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
