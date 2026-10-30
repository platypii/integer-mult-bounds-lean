module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedFullLineCoupling
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryData

/-! Feed the executed periodic residual endpoint to boundary selection and folding. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem periodicBoundaryData_exec {Q A V s t band a b precision q w u : ℕ} [NeZero s] {P U : Type}
    {body : P → Pr P 168 Q A U} (v : HS 168 Q A U) (S : Stacks 168 A)
    (D : ZMod s → GaussianInt) (rhsTail raw : List (Fin (A+4)))
    (hready : RetainedCouplingReady precision q w s t u band a b raw
      (embStk groupReg (embStk intervalPageReg S)))
    (hV : (S.R 163).length = V)
    (hbase : ∀ k ∈ [(145 : Fin 168),146,147,149,151,155,165],
      S.R k = binSyms V (couplingIntervalValue s t band a b 0 s k))
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hA : 4 ≤ A)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) (hfitV : (s+2*band)+s < 2^V)
    (hwidth : (S.R 130).length = w) (h167 : S.R 167 = []) (h143 : S.R 143 = []) :
    let R := fullLineCouplingResult S V band s (cstream A w (packedInterval 0 s D)) rhsTail
    ∃ v' n, v'.user = v.user ∧ n ≤ packedBoundaryDataCost V s (haloBoundary s t band a b).card w ∧
      Exec body packedBoundaryData (mk v R) n
        (mk v' {R with R := (Function.update (Function.update (Function.update R.R
          167 (couplingSourceIntervalMaskSymbols true A s t band a b 0 s))
          116 (List.replicate (haloBoundary s t band a b).card tick))
          143 (cstream A w ((bFoldOrder s (haloBoundary s t band a b)).map D)))}) := by
  dsimp only
  apply packedBoundaryData_exec (body := body) v _ (fullLineCouplingResult_metadata S _ _ hV hbase)
    (by omega) hst haS hbS hA hwide (by simpa using hfitV)
  · intro k hk
    let i : Fin 117 := ⟨k.val,by omega⟩
    have hi := hready.boundaryScratch i hk
    simpa [fullLineCouplingResult,completedCouplingIntervalR,embStk,groupReg,intervalPageReg,
      Function.update_apply,Fin.ext_iff,i,show k.val ≠ 93 by omega,show k.val ≠ 110 by omega,
      show k.val ≠ 141 by omega,show k.val ≠ 148 by omega,show k.val ≠ 154 by omega,
      show k.val ≠ 156 by omega,show k.val ≠ 160 by omega,show k.val ≠ 164 by omega] using hi
  · intro i _
    exact ⟨Nat.zero_le _,by simpa using i.val_lt⟩
  · exact fullLineCouplingResult_source ..
  · simpa [fullLineCouplingResult,completedCouplingIntervalR] using h167
  · simpa [fullLineCouplingResult,completedCouplingIntervalR] using hwidth
  · have hh := hready.fresh 116 (by simp)
    simpa [fullLineCouplingResult,completedCouplingIntervalR,embStk,groupReg,intervalPageReg] using hh
  · simpa [fullLineCouplingResult,completedCouplingIntervalR] using h143

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
