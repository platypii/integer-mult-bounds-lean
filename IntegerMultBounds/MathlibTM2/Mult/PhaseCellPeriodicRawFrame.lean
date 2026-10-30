module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPeriodicPreparationFrame

/-! The preparation retains the native queue used to restore the original RHS. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast ScalarPlacement

theorem periodicRuntimeBank_raw {A : ℕ} (precision q s t u band : ℕ) (S : Stacks 242 A) :
    (periodicRuntimeBank precision q s t u band S).R 110 = S.R 110 := by
  let e : Fin 144 → Fin 242 := Fin.castLE (by decide)
  let T := embStk e S
  let H := embOvr e ({T with R := couplingHeadersR precision q s t u band 0 s T.R} : Stacks 144 A).get S
  let c : Fin 117 → Fin 242 := Fin.castLE (by decide)
  let K := embStk c H
  let G := embOvr c ({K with R := counterR q (2*q+8) K.R} : Stacks 117 A).get H
  change G.R 110 = S.R 110
  have he : Function.Injective e := by
    intro i j hh; exact Fin.ext (congrArg (fun k : Fin 242 => k.val) hh)
  have hc : Function.Injective c := by
    intro i j hh; exact Fin.ext (congrArg (fun k : Fin 242 => k.val) hh)
  have hh := embOvr_get he ({T with R := couplingHeadersR precision q s t u band 0 s T.R} : Stacks 144 A).get S (.rt 110)
  change H.R 110 = (couplingHeadersR precision q s t u band 0 s T.R 110).map id at hh
  rw [List.map_id,couplingHeadersR_off precision q s t u band 0 s T.R 110 (by decide)] at hh
  change H.R 110 = S.R 110 at hh
  have hk := embOvr_get hc ({K with R := counterR q (2*q+8) K.R} : Stacks 117 A).get H (.rt 110)
  change G.R 110 = (counterR q (2*q+8) K.R 110).map id at hk
  have hg : G.R 110 = H.R 110 := by
    simpa [counterR,cr,ShortConv.OutputPlacement.code,K,embStk,c] using hk
  exact hg.trans hh

theorem periodicPreparedProducerBank_raw {A s : ℕ} [NeZero s] (p q t u band : ℕ) (S : Stacks 242 A) :
    (periodicPreparedProducerBank p q s t u band S).R 110 = S.R 110 := by
  dsimp only [periodicPreparedProducerBank]
  rw [periodicGeometrySeed_frame _ 110 (by decide)]
  simp only [periodicIterateBank,Function.update_of_ne (show (110 : Fin 242) ≠ 141 by decide),
    Function.update_of_ne (show (110 : Fin 242) ≠ 132 by decide)]
  rw [periodicRuntimeBank_raw]
  simp [periodicCouplingPageBank,periodicCouplingWidthBank]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
