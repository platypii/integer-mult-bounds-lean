module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedCouplingHeaders

/-! The packed interior's retained state is the coupling solver's input state
through the existing static header view. No header copies are needed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node

/-- Canonical geometry is outside the shared-header permutation. -/
theorem couplingIntervalMetadata_shared {A V s t band a b origin N : ℕ} {S : Stacks 168 A}
    (h : CouplingIntervalMetadata V s t band a b origin N S) :
    CouplingIntervalMetadata V s t band a b origin N (embStk sharedCouplingReg S) := by
  constructor
  · simpa only [embStk_R,sharedCouplingReg_high 163 (by decide)] using h.width
  · intro k hk
    have hh : 143 ≤ k.val := by
      simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa only [embStk_R,sharedCouplingReg_high k hh] using h.encoded k hk

/-- Read retained dimensions in place after the complete interior execution. -/
theorem PackedHaloReady.coupling {A precision stage q l s t u band a b V w : ℕ}
    {input E outputTail : List (Fin (A+4))} {S : Stacks 168 A}
    (h : PackedHaloReady precision stage q l s t u band a b V w input E outputTail S)
    (ha : (S.R 141).length = a) (hb : (S.R 142).length = b)
    (hleft : ∀ k ∈ [(121 : Fin 168),122,123,124], S.L k = []) :
    CouplingReady precision q w s t u band a b input (embStk sharedCouplingCoreReg S) := by
  have hp : (S.R 117).length = precision := by
    simpa [packedHeaderReg,groupHeaderValue] using h.masters (117,114) (by decide) (by decide)
  have hq : (S.R 119).length = q := by
    simpa [packedHeaderReg,groupHeaderValue] using h.masters (119,112) (by decide) (by decide)
  have hs : (S.R 121).length = s := by
    simpa [packedHeaderReg,groupHeaderValue] using h.masters (121,97) (by decide) (by decide)
  have ht : (S.R 122).length = t := by
    simpa [packedHeaderReg,groupHeaderValue] using h.masters (122,98) (by decide) (by decide)
  have hu : (S.R 123).length = u := by
    simpa [packedHeaderReg,groupHeaderValue] using h.masters (123,99) (by decide) (by decide)
  have hband : (S.R 124).length = band := by
    simpa [packedHeaderReg,groupHeaderValue] using h.masters (124,100) (by decide) (by decide)
  simpa only [List.nil_append] using sharedCouplingHeaders_ready S [] input (S.R 93) S.inp S.out
    h.native hp hq hs ht hu hband ha hb h.wordWidth hleft

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
