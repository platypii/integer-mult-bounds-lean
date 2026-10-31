module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalOriginPackets

/-! Project either coordinate of a table packet without decoding its value. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast.TableVM

theorem tblPairs_fst_bits {A V x y : ℕ} (hA : 4 ≤ A) (hx : x < 2^V) :
    (tblPairs A V x y).map (fun sym => bitSymbol (pairRe sym)) = binSyms (A := A) V x := by
  simp [tblPairs,coeffSyms,binSyms,List.map_ofFn,Function.comp_def,pairRe_pairSym hA,Nat.mod_eq_of_lt hx]

theorem tblPairs_snd_bits {A V x y : ℕ} (hA : 4 ≤ A) (hy : y < 2^V) :
    (tblPairs A V x y).map (fun sym => bitSymbol (pairIm sym)) = binSyms (A := A) V y := by
  simp [tblPairs,coeffSyms,binSyms,List.map_ofFn,Function.comp_def,pairIm_pairSym hA,Nat.mod_eq_of_lt hy]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
