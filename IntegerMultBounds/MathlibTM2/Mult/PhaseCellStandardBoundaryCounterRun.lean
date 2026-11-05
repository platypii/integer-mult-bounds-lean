module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStandardBoundaryCounters

/-! Execute boundary metadata directly into the standard seam master tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix BoundaryCropMetadata
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

theorem standardBoundaryCounters_exec (last : Bool)
    (D s width W : ℕ) (st : TblSt 9 A)
    (hs : st.val 0 = s) (hw : st.val 1 = width) (hW : st.val 2 = W)
    (hwidth : 0 < width) (hword : 0 < W) (hroom : 3*width < s)
    (hfit : s*W < 2^D) (hvalues : ∀ j, st.val j < 2^D)
    (wl : List (Fin (A+4))) (hwl : wl.length = D)
    (v : HS 117 Q A U) (S : Stacks 117 A) (hholds : tblHolds boundaryCounterRegister S (tblRho D wl [] st))
    (hblank : S.R 26 = [] ∧ S.R 24 = []) :
    ∃ v' F n z, v'.user = v.user ∧ n ≤ 10*tblC D 0+6*(s*W)+22*D+13 ∧
      Exec body (standardBoundaryCounterProgram last) (mk v S) n (mk v' F) ∧
      tblHolds boundaryCounterRegister F (tblRho D wl [] z) ∧
      (∀ i : Fin 3, z.val (Fin.castAdd 6 i) = st.val (Fin.castAdd 6 i)) ∧ z.acc = st.acc ∧
      (∀ j, z.val j < 2^D) ∧
      F.R 26 = List.replicate (coreStart width (index last s width)*W) tick ∧
      F.R 24 = List.replicate (coreLength s width (index last s width)*W) tick ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ k, (∀ r, boundaryCounterRegister r ≠ k) → k ≠ 26 → k ≠ 24 → F.R k = S.R k := by
  simpa only [standardBoundaryCounterProgram,hblank.1,hblank.2,List.append_nil] using
    (BoundaryCropMetadata.counters_exec (body := body) boundaryCounterRegister
      boundaryCounterRegister_injective last 26 24 (by decide)
      (fun r => (boundaryCounterRegister_off_masters r).1)
      (fun r => (boundaryCounterRegister_off_masters r).2)
      D s width W st hs hw hW hwidth hword hroom hfit hvalues wl hwl v S hholds)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
