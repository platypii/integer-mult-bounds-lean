module

public import IntegerMultBounds.MathlibTM2.Host.PrefixFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPeriodicProducerPreparation

/-! The executed preparation retains the base geometry and consumes the iterate
archive. These structural facts supply the recovery publisher. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast ScalarPlacement

theorem periodicRuntimeBank_high {A : ℕ} (precision q s t u band : ℕ)
    (S : Stacks 242 A) (k : Fin 242) (hk : 144 ≤ k.val) :
    (periodicRuntimeBank precision q s t u band S).R k = S.R k := by
  dsimp only [periodicRuntimeBank]
  rw [embOvr_prefix_right (by decide : 117 ≤ 242) _ _ k (by omega)]
  exact embOvr_prefix_right (by decide : 144 ≤ 242) _ S k hk

theorem periodicPreparedProducerBank_base {A s : ℕ} [NeZero s] (p q t u band : ℕ)
    (S : Stacks 242 A) (k : Fin 242) (hk : 145 ≤ k.val)
    (hnot : k ∉ periodicGeometryDerived) :
    (periodicPreparedProducerBank p q s t u band S).R k = S.R k := by
  dsimp only [periodicPreparedProducerBank]
  rw [periodicGeometrySeed_frame _ k hnot]
  have hn : k.val ≠ 130 ∧ k.val ≠ 132 ∧ k.val ≠ 135 ∧ k.val ≠ 138 ∧
      k.val ≠ 139 ∧ k.val ≠ 140 ∧ k.val ≠ 141 ∧ k.val ≠ 143 := by omega
  simp only [periodicIterateBank,Function.update_of_ne
    (show k ≠ 132 from fun he => hn.2.1 (congrArg Fin.val he)),
    Function.update_of_ne (show k ≠ 141 from fun he => hn.2.2.2.2.2.2.1 (congrArg Fin.val he))]
  rw [periodicRuntimeBank_high _ _ _ _ _ _ _ k (by omega)]
  simp [periodicCouplingPageBank,periodicCouplingWidthBank,Fin.ext_iff,
    hn.1,hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2.1,hn.2.2.2.2.2.1,hn.2.2.2.2.2.2.2]

theorem periodicPreparedProducerBank_archive {A s : ℕ} [NeZero s] (p q t u band : ℕ)
    (S : Stacks 242 A) : (periodicPreparedProducerBank p q s t u band S).R 132 = [] := by
  simp [periodicPreparedProducerBank,periodicGeometrySeed,periodicGeometryDerived,periodicIterateBank]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
