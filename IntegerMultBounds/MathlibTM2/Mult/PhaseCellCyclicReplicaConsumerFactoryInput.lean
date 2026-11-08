module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaConsumerExport
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicResidualBatchFrame

/-! Export restores the original factor workspace, apart from the produced
residual packets and their count. Factory readiness therefore comes from the
ordinary input bank, before either cached pass executes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open CyclicReplicaPlacement

theorem cyclicReplicaConsumerExport_factoryInput
    {A p l s t u target a n : ℕ} [NeZero s]
    {tail pageTail : List (Fin (A+4))} (S : Stacks 834 A) (B : Stacks 234 A)
    (rows : List (Fin (A+4)))
    (factory : CyclicResidualBatchInput p l s t u target a n tail pageTail B)
    (hin : S.inp = B.inp) (hout : S.out = B.out) (hL : (embStk factorReg S).L = B.L)
    (hR : ∀ k : Fin 234, k ≠ 170 → k ≠ 173 → S.R (factorReg k) = B.R k) :
    CyclicResidualBatchInput p l s t u target a n tail pageTail
      (embStk factorReg (cyclicReplicaConsumerExportState S rows)) := by
  have hblank : ∀ k ∈ cyclicResidualRowsRetired, B.R k = [] := by
    intro k hk
    simp only [cyclicResidualRowsRetired,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · apply List.eq_nil_of_length_eq_zero
      simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,
        preparedBoundaryCoreReg,preparedBoundaryBatchCoreReg] using factory.arithmetic.wordWidth
    all_goals first
      | exact factory.new 168 (by decide)
      | exact factory.new 169 (by decide)
      | exact factory.new 170 (by decide)
      | exact factory.new 171 (by decide)
      | exact factory.new 172 (by decide)
      | exact factory.new 173 (by decide)
  rw [cyclicReplicaConsumerExportState_factor]
  apply factory.of_packet_frame
  · exact hin
  · exact hout
  · exact hL
  · intro k hk226 hk229
    by_cases hretired : k ∈ cyclicResidualRowsRetired
    · simp only [exportedCyclicResidualRows,ite_eq_left hretired]
      exact (hblank k hretired).symm
    · have hoff : k ∉ [(130 : Fin 234),168,169,171,172,229] := by
        simp only [cyclicResidualRowsRetired,List.mem_cons,List.not_mem_nil,or_false,not_or] at hretired
        simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
        exact ⟨hretired.1,hretired.2.1,hretired.2.2.1,hretired.2.2.2.2.1,
          hretired.2.2.2.2.2.1,hk229⟩
      have h170 : k ≠ 170 := by intro he; subst k; exact hretired (by decide)
      have h173 : k ≠ 173 := by intro he; subst k; exact hretired (by decide)
      change (if k ∈ cyclicResidualRowsRetired then [] else
        Function.update (embStk factorReg (cyclicReplicaConsumerState S)).R 226 rows k) = B.R k
      rw [ite_eq_right hretired,Function.update_of_ne hk226]
      exact (cyclicReplicaConsumerState_factor_read S k hoff).trans (hR k h170 h173)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
