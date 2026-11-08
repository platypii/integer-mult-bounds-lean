module

public import IntegerMultBounds.MathlibTM2.Fast.TableVM

/-! Convert a table packet's real component to ordinary binary metadata. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast.TableVM

theorem tblPairs_real_bits {A V origin : ℕ} (hA : 4 ≤ A) (hfit : origin < 2^V) :
    (tblPairs A V origin 0).map (fun sym => bitSymbol (pairRe sym)) = binSyms (A := A) V origin := by
  simp [tblPairs, coeffSyms, binSyms, List.map_ofFn, Function.comp_def, pairRe_pairSym hA, Nat.mod_eq_of_lt hfit]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
