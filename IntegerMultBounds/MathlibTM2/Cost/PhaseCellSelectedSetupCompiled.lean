module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupTrace
public import IntegerMultBounds.MathlibTM2.StackCompileInvariant

/-! The selected setup lifecycle's stock bound holds on the compiled TM2,
 including entry, nested calls, return and halt. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

/-- Any procedure-table placement of the actual setup lifecycle inherits its
whole-volume stock allowance on every compiled configuration. -/
theorem selectedFamilySetup_compiled_volume_le {Q A : ℕ} {P U : Type} [Fintype P]
    (body : P → Pr P 263 Q A U) (main : P) (ct : ℕ) (recovery : Bool)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (hmain : body main = generatedClosedFamilyComplexBatch recovery hR hQ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ key : SelectedFamilyKey n i ct,
      PhaseCellBand.width (Sizes.p n) key.1 ≤ Sizes.s n i →
      ∀ (s t : Store (HΓ (T := 263) A) (HS 263 Q A U)) (steps : ℕ),
      steps ≤ generatedClosedFamilyComplexBatchCost A (Sizes.p n) key.1
        (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) (Sizes.t n i)
        key.2.2.1 key.2.2.2 key.2.1 0 →
      Exec body (generatedClosedFamilyComplexBatch recovery hR hQ) s steps t →
      ReachWithin (mcode body main) (fun c => compiledSize body c ≤ mnSize s+1+Sizes.T n)
        (cfg (some .entry) s none []) (steps+2) (cfg none t none []) := by
  filter_upwards [selectedFamilySetup_trace_volume_le body ct recovery hR hQ] with n hn
  intro h i _ key hband s t steps hsteps he
  have hw := hn h i key hband s t steps 1 hsteps he
  rw [← hmain] at hw
  exact hw.stock_run_main

end IntegerMultBounds.MathlibTM2.Cost
