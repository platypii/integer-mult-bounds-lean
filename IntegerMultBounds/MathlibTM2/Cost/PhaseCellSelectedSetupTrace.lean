module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupKeys
public import IntegerMultBounds.MathlibTM2.StackCallResources

/-! Setup lifecycle traces, including all data stacks and outstanding calls.
 This does not supply the repeated-line workspace bound. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

/-- The existing empty-batch lifecycle's executed time certificate yields an
invariant at every intermediate store, including nested arithmetic calls. -/
theorem selectedFamilySetup_trace_volume_le {Q A : ℕ} {P U : Type} [Fintype P]
    (body : P → Pr P 263 Q A U) (ct : ℕ) (recovery : Bool)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ key : SelectedFamilyKey n i ct,
      PhaseCellBand.width (Sizes.p n) key.1 ≤ Sizes.s n i →
      ∀ (s t : Store (HΓ (T := 263) A) (HS 263 Q A U)) (steps depth : ℕ),
      steps ≤ generatedClosedFamilyComplexBatchCost A (Sizes.p n) key.1
        (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) (Sizes.t n i)
        key.2.2.1 key.2.2.2 key.2.1 0 →
      Exec body (generatedClosedFamilyComplexBatch recovery hR hQ) s steps t →
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize s+depth+Sizes.T n)
        depth (generatedClosedFamilyComplexBatch recovery hR hQ) s steps t := by
  let c := max (mnProgPush (generatedClosedFamilyComplexBatch (P := P) (U := U)
    (A := A) recovery hR hQ)) (mnPushC body)
  filter_upwards [selectedFamilyAllKeysSetup_scaled_volume_le ct (c+1)] with n hn
  intro h i _ key hband s t steps depth hsteps he
  have hcost : steps ≤ selectedFamilyKeySetupCost n i ct A key := by
    rw [selectedFamilyKeySetupCost,if_pos hband]
    exact hsteps.trans (generatedClosedFamilyComplexBatchCost_setup_le (h.good.lt i)
      A (Sizes.p n) key.1 (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
      key.2.2.1 key.2.2.2 key.2.1)
  have hsum : selectedFamilyKeySetupCost n i ct A key ≤
      ∑ k : SelectedFamilyKey n i ct, selectedFamilyKeySetupCost n i ct A k :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ key)
  have hspace := (Nat.mul_le_mul_left (c+1) (hcost.trans hsum)).trans (hn h i A)
  apply (mn_exec_finite_within he (budget := steps) (depth := depth) le_rfl).mono
  intro d z hz
  exact hz.trans (Nat.add_le_add_left hspace _)

end IntegerMultBounds.MathlibTM2.Cost
