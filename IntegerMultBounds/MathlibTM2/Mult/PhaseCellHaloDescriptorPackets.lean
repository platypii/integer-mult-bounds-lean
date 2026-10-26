module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalOriginPackets
public import IntegerMultBounds.NLogN.PhaseCellHaloInterval

/-! Binary origin/length packets for the positive clipped cells, in ambient
phase order. Each descriptor occupies exactly two fixed-width words. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def haloDescriptorPackets (A V s t band a b : ℕ) : List (Fin (A+4)) :=
  (haloCellPhases s t band a b).flatMap (fun phase =>
    binSyms V (haloStart s t band a phase) ++ binSyms V (haloLength s t band a b phase))

theorem haloDescriptorPairs_real_bits {A V s t band a b : ℕ}
    (hA : 4 ≤ A) (hs : s < 2^V) :
    ((haloCellPhases s t band a b).flatMap (fun phase =>
      tblPairs A V (haloStart s t band a phase) 0 ++
      tblPairs A V (haloLength s t band a b phase) 0)).map
      (fun sym => bitSymbol (pairRe sym)) = haloDescriptorPackets A V s t band a b := by
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro phase hp
  have hpos := ((mem_haloCellPhases s t band a b phase).mp hp).2
  have hstop := haloStop_le s t band b phase
  have hstart : haloStart s t band a phase < 2^V := by
    dsimp only [haloLength] at hpos
    omega
  have hlen : haloLength s t band a b phase < 2^V := by
    dsimp only [haloLength]
    omega
  exact List.map_append.trans
    (congrArg₂ List.append (tblPairs_real_bits hA hstart) (tblPairs_real_bits hA hlen))

@[simp] theorem haloDescriptorPackets_length (A V s t band a b : ℕ) :
    (haloDescriptorPackets A V s t band a b).length =
      (haloCellPhases s t band a b).length * (2*V) := by
  simp [haloDescriptorPackets,List.length_flatMap,Nat.two_mul]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
