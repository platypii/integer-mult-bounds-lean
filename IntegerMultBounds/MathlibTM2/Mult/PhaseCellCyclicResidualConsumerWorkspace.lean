module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicResidualBatchInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExportCyclicResidualRows

/-! The ordinary factor-input contract already supplies the consumer workspace.
Only the two owned packet/count destinations need separate initial emptiness. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem CyclicResidualBatchInput.consumerWorkspace
    {A p l s t u target a n : ℕ} [NeZero s]
    {tail pageTail : List (Fin (A+4))} {S : Stacks 234 A}
    (h : CyclicResidualBatchInput p l s t u target a n tail pageTail S)
    (h226 : S.R 226 = []) (h229 : S.R 229 = []) :
    (∀ k ∈ [(130 : Fin 234),168,169,171,172,174,175,229], S.R k = []) ∧
    S.R 170 = [] ∧ S.R 173 = [] ∧
    (∀ r : Fin 180, r.val < 80 → S.R (cyclicResidualRowsReg r) = []) ∧
    (∀ r ∈ [(134 : Fin 180),135,136,137,143,174,175,176,177,178],
      S.R (cyclicResidualRowsReg r) = []) := by
  have h130 : S.R 130 = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,
      preparedBoundaryCoreReg,preparedBoundaryBatchCoreReg] using h.arithmetic.wordWidth
  have hnew (k : Fin 224) (hk : 154 ≤ k.val) : S.R ⟨k.val,by omega⟩ = [] := h.new k hk
  have hlow (k : Fin 234) (hk : k.val < 80) : S.R k = [] := by
    let i : Fin 144 := ⟨k.val,by omega⟩
    have hi117 : i.val < 117 := by change k.val < 117; omega
    have hi93 : i ≠ 93 := by intro he; have hv := congrArg Fin.val he; change k.val = 93 at hv; omega
    have hi110 : i ≠ 110 := by intro he; have hv := congrArg Fin.val he; change k.val = 110 at hv; omega
    have h109 : k.val ≠ 109 := by omega
    have h115 : k.val ≠ 115 := by omega
    have h116 : k.val ≠ 116 := by omega
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,
      preparedBoundaryCoreReg,preparedBoundaryBatchCoreReg,i,Fin.ext_iff,h109,h115,h116]
      using h.arithmetic.blank i hi117 hi93 hi110
  refine ⟨?_,hnew 170 (by decide),hnew 173 (by decide),?_,?_⟩
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h130
    all_goals first
      | exact h229
      | exact hnew 168 (by decide)
      | exact hnew 169 (by decide)
      | exact hnew 171 (by decide)
      | exact hnew 172 (by decide)
      | exact hnew 174 (by decide)
      | exact hnew 175 (by decide)
  · intro r hr
    by_cases h6 : r = 6
    · subst r; simpa [cyclicResidualRowsReg] using h226
    · have h179 : r ≠ 179 := by intro he; have hv := congrArg Fin.val he; simp at hv; omega
      exact hlow _ (by simpa [cyclicResidualRowsReg,h6,h179] using hr)
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,
          preparedBoundaryCoreReg,preparedBoundaryBatchCoreReg,cyclicResidualRowsReg]
          using h.arithmetic.fresh 134 (by simp)
      | simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,
          preparedBoundaryCoreReg,preparedBoundaryBatchCoreReg,cyclicResidualRowsReg]
          using h.arithmetic.fresh 135 (by simp)
      | simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,
          preparedBoundaryCoreReg,preparedBoundaryBatchCoreReg,cyclicResidualRowsReg]
          using h.arithmetic.fresh 136 (by simp)
      | simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,
          preparedBoundaryCoreReg,preparedBoundaryBatchCoreReg,cyclicResidualRowsReg]
          using h.arithmetic.fresh 137 (by simp)
      | simpa [cyclicResidualRowsReg] using h.fresh 143 (by simp)
      | simpa [cyclicResidualRowsReg] using hnew 174 (by decide)
      | simpa [cyclicResidualRowsReg] using hnew 175 (by decide)
      | simpa [cyclicResidualRowsReg] using hnew 176 (by decide)
      | simpa [cyclicResidualRowsReg] using hnew 177 (by decide)
      | simpa [cyclicResidualRowsReg] using hnew 178 (by decide)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
