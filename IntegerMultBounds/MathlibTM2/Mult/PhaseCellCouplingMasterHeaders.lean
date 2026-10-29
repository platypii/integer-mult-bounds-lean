module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedCouplingHeaders

/-! The small retained header interface shared by both Schur coupling passes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

structure CouplingMasterHeaders {A : ℕ} (P q w s t u band a b : ℕ) (S : Stacks 168 A) : Prop where
  precision : (S.R 117).length = P
  fraction : (S.R 119).length = q
  axis : (S.R 121).length = s
  period : (S.R 122).length = t
  parameter : (S.R 123).length = u
  bandwidth : (S.R 124).length = band
  lower : (S.R 141).length = a
  upper : (S.R 142).length = b
  width : (S.R 130).length = w

def couplingMasterPorts : List (Fin 168) := [117,119,121,122,123,124,141,142,130]

theorem CouplingMasterHeaders.of_frame {A P q w s t u band a b : ℕ} {S F : Stacks 168 A}
    (h : CouplingMasterHeaders P q w s t u band a b S)
    (hframe : ∀ k ∈ couplingMasterPorts, F.R k = S.R k) :
    CouplingMasterHeaders P q w s t u band a b F := by
  constructor
  · rw [hframe 117 (by decide)]; exact h.precision
  · rw [hframe 119 (by decide)]; exact h.fraction
  · rw [hframe 121 (by decide)]; exact h.axis
  · rw [hframe 122 (by decide)]; exact h.period
  · rw [hframe 123 (by decide)]; exact h.parameter
  · rw [hframe 124 (by decide)]; exact h.bandwidth
  · rw [hframe 141 (by decide)]; exact h.lower
  · rw [hframe 142 (by decide)]; exact h.upper
  · rw [hframe 130 (by decide)]; exact h.width

/-- Once the native scratch is released, the retained headers directly supply
coupling readiness; no physical header copies are needed. -/
theorem CouplingMasterHeaders.ready {A P q w s t u band a b : ℕ} {S : Stacks 168 A}
    (h : CouplingMasterHeaders P q w s t u band a b S)
    (hleft : ∀ i : Fin 117, S.L (packedCellCoreReg i) = [])
    (hblank : ∀ i : Fin 117, i ≠ 93 → i ≠ 110 → S.R (packedCellCoreReg i) = [])
    (hmasterLeft : ∀ k ∈ ([(121 : Fin 168),122,123,124]), S.L k = []) :
    CouplingReady P q w s t u band a b (S.R 110) (embStk sharedCouplingCoreReg S) := by
  have hbank : embStk packedCellCoreReg S =
      releasedCellBank [] (S.R 110) (S.R 93) S.inp S.out := by
    refine Stacks.ext rfl rfl ?_ ?_
    · funext i; exact hleft i
    · funext i
      by_cases h93 : i = 93
      · subst i; rfl
      by_cases h110 : i = 110
      · subst i; rfl
      have hv93 : i.val ≠ 93 := fun he => h93 (Fin.ext he)
      have hv110 : i.val ≠ 110 := fun he => h110 (Fin.ext he)
      simpa [embStk,releasedCellBank,hv93,hv110] using hblank i h93 h110
  simpa only [List.nil_append] using sharedCouplingHeaders_ready S [] (S.R 110) (S.R 93)
    S.inp S.out hbank h.precision h.fraction h.axis h.period h.parameter h.bandwidth
    h.lower h.upper h.width hmasterLeft

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
