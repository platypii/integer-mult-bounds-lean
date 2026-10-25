module

public import IntegerMultBounds.NLogN.PhaseCellNaturalGroups
public import IntegerMultBounds.MathlibTM2.Fast.TableVM

/-! The natural schedule's emitted origins agree, in order and representation,
with the binary control row ABI of the closed batch solver. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def naturalOriginPackets (A V s t band L : ℕ) : List (Fin (A+4)) :=
  (naturalLengthGroup s t band L).flatMap (fun phase => binSyms V (naturalStart s t band phase))

theorem naturalOriginPackets_eq_rows {A s : ℕ} [NeZero s] (V t band L : ℕ) :
    naturalOriginPackets A V s t band L =
      (List.range (naturalLengthGroup s t band L).length).flatMap
        (fun n => binSyms V (naturalGroupOrigin s t band L n).val) := by
  have hflat {K : Type} (xs : List ℕ) (F : ℕ → List K) :
      (List.range xs.length).flatMap (fun n => F (xs.getD n 0)) = xs.flatMap F := by
    induction xs with
    | nil => simp
    | cons x xs ih => simpa [List.range_succ_eq_map, List.flatMap_map] using congrArg (F x ++ ·) ih
  unfold naturalOriginPackets
  rw [← hflat (naturalLengthGroup s t band L) (fun phase => binSyms V (naturalStart s t band phase))]
  apply List.flatMap_congr
  intro n hn
  rw [naturalGroupOrigin_val band L ⟨n, List.mem_range.mp hn⟩]
  rfl

theorem tblPairs_real_bits {A V origin : ℕ} (hA : 4 ≤ A) (hfit : origin < 2^V) :
    (tblPairs A V origin 0).map (fun sym => bitSymbol (pairRe sym)) = binSyms (A := A) V origin := by
  simp [tblPairs, coeffSyms, binSyms, List.map_ofFn, Function.comp_def, pairRe_pairSym hA, Nat.mod_eq_of_lt hfit]

theorem naturalOriginPairs_real_bits {A V s t band L : ℕ} (hA : 4 ≤ A) (hs : s ≤ 2^V) :
    ((naturalLengthGroup s t band L).flatMap (fun phase => tblPairs A V (naturalStart s t band phase) 0)).map
      (fun sym => bitSymbol (pairRe sym)) = naturalOriginPackets A V s t band L := by
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro phase hp
  obtain ⟨_, hL, hlen⟩ := (mem_naturalLengthGroup s t band L phase).mp hp
  exact tblPairs_real_bits hA ((naturalStart_lt band phase (by omega)).trans_le hs)

@[simp] theorem naturalOriginPackets_length (A V s t band L : ℕ) :
    (naturalOriginPackets A V s t band L).length = (naturalLengthGroup s t band L).length*V := by
  simp [naturalOriginPackets, List.length_flatMap]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
