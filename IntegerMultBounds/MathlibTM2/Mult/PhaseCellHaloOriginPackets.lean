module

public import IntegerMultBounds.NLogN.PhaseCellHaloGroups
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalOriginPackets
public import IntegerMultBounds.MathlibTM2.Fast.TableVM

/-! The halo group schedule's emitted origins agree, in order and representation,
with the binary control row ABI of the closed batch solver. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def haloOriginPackets (A V s t band a b L : ℕ) : List (Fin (A+4)) :=
  (haloLengthGroup s t band a b L).flatMap (fun phase => binSyms V (haloStart s t band a phase))

theorem haloOriginPackets_eq_rows {A s : ℕ} [NeZero s] (V t band a b L : ℕ) :
    haloOriginPackets A V s t band a b L =
      (List.range (haloLengthGroup s t band a b L).length).flatMap
        (fun n => binSyms V (haloGroupOrigin s t band a b L n).val) := by
  have hflat {K : Type} (xs : List ℕ) (F : ℕ → List K) :
      (List.range xs.length).flatMap (fun n => F (xs.getD n 0)) = xs.flatMap F := by
    induction xs with
    | nil => simp
    | cons x xs ih => simpa [List.range_succ_eq_map, List.flatMap_map] using congrArg (F x ++ ·) ih
  unfold haloOriginPackets
  rw [← hflat (haloLengthGroup s t band a b L) (fun phase => binSyms V (haloStart s t band a phase))]
  apply List.flatMap_congr
  intro n hn
  rw [haloGroupOrigin_val band a b L ⟨n, List.mem_range.mp hn⟩]
  rfl

theorem haloOriginPairs_real_bits {A V s t band a b L : ℕ} (hA : 4 ≤ A) (hs : s ≤ 2^V) :
    ((haloLengthGroup s t band a b L).flatMap (fun phase => tblPairs A V (haloStart s t band a phase) 0)).map
      (fun sym => bitSymbol (pairRe sym)) = haloOriginPackets A V s t band a b L := by
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro phase hp
  obtain ⟨_, hL, hlen⟩ := (mem_haloLengthGroup s t band a b L phase).mp hp
  have hstop := haloStop_le s t band b phase
  have hstart : haloStart s t band a phase < s := by
    dsimp only [haloLength] at hlen
    omega
  exact tblPairs_real_bits hA (hstart.trans_le hs)

@[simp] theorem haloOriginPackets_length (A V s t band a b L : ℕ) :
    (haloOriginPackets A V s t band a b L).length = (haloLengthGroup s t band a b L).length*V := by
  simp [haloOriginPackets, List.length_flatMap]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
