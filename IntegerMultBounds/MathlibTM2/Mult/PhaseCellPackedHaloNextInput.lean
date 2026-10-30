module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloBetweenInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedPackedHaloRealBoundaryData

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast ScalarPlacement

variable {A P stage q l s t u band a b V w W boundaryCount : ℕ} {S : Stacks 248 A}

/-- Every left tape used by the native producer and header copies is restored. -/
theorem PackedHaloBetweenInputs.left_low
    (h : PackedHaloBetweenInputs P stage q l s t u band a b V w W boundaryCount S)
    (i : Fin 248) (hi : i.val < 140) : S.L i = [] := by
  have hh := h.bank.workspace.left ⟨i.val,by omega⟩
  simpa [embStk,packedBoundaryRecoveryBase,preparedBoundaryCoreReg,packedBoundaryFactorReg,
    Fin.ext_iff,show i.val ≠ 140 by omega,show i.val ≠ 143 by omega,
    show i.val ≠ 206 by omega,show i.val < 154 by omega] using hh

/-- The next source suffix is already in the producer's native input format. -/
theorem PackedHaloBetweenInputs.native_bank
    (h : PackedHaloBetweenInputs P stage q l s t u band a b V w W boundaryCount S)
    (input : List (Fin (A+4))) (hsource : S.R 110 = input) :
    embStk packedCellCoreReg (embStk packedRecoveryRuntimeReg S) =
      releasedCellBank [] input (S.R 93) S.inp S.out := by
  refine Stacks.ext rfl rfl ?_ ?_
  · funext i
    exact h.left_low ⟨i.val,by omega⟩ (by change i.val < 140; have hi := i.isLt; omega)
  · funext i
    have hi := i.isLt
    by_cases h93 : i = 93
    · subst i; simp [embStk,packedCellCoreReg,packedRecoveryRuntimeReg,releasedCellBank]
    by_cases h110 : i = 110
    · subst i; simpa [embStk,packedCellCoreReg,packedRecoveryRuntimeReg,releasedCellBank] using hsource
    have h93v : i.val ≠ 93 := fun he => h93 (Fin.ext he)
    have h110v : i.val ≠ 110 := fun he => h110 (Fin.ext he)
    simpa [embStk,packedCellCoreReg,packedRecoveryRuntimeReg,releasedCellBank,h93v,h110v]
      using h.native i h93 h110

/-- The native master-copy schedule is determined by the retained header record
and the cleared selected-length header. -/
theorem PackedHaloBetweenInputs.master_copies
    (h : PackedHaloBetweenInputs P stage q l s t u band a b V w W boundaryCount S) :
    ∀ r ∈ groupHeaderCopies,
      ((embStk packedRecoveryRuntimeReg S).R (packedHeaderReg r.1)).length =
        groupHeaderValue P stage q l s t u band 0 r.1 := by
  intro r hr
  simp only [groupHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [packedHeaderReg,groupHeaderValue] using h.headers.masters.precision
  · simpa [packedHeaderReg,groupHeaderValue] using h.headers.stage
  · simpa [packedHeaderReg,groupHeaderValue] using h.headers.masters.fraction
  · simpa [packedHeaderReg,groupHeaderValue] using h.headers.level
  · simpa [packedHeaderReg,groupHeaderValue] using h.headers.masters.axis
  · simpa [packedHeaderReg,groupHeaderValue] using h.headers.masters.period
  · simpa [packedHeaderReg,groupHeaderValue] using h.headers.masters.parameter
  · simpa [packedHeaderReg,groupHeaderValue] using h.headers.masters.bandwidth
  · simp [packedHeaderReg,groupHeaderValue,embStk,packedRecoveryRuntimeReg,h.scratch 128 (by decide)]
  · simp [packedHeaderReg,groupHeaderValue,embStk,packedRecoveryRuntimeReg,h.scratch 128 (by decide)]

/-- No workspace reallocation is required between executions. -/
theorem PackedHaloBetweenInputs.eq_extend
    (h : PackedHaloBetweenInputs P stage q l s t u band a b V w W boundaryCount S) :
    S = extendStacks (by decide) (embStk packedBoundaryRecoveryBase S) := by
  apply eq_extendStacks (by decide)
  · rfl
  · exact h.privateBank

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
