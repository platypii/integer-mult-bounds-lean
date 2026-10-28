module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedBatchStepTrace
public import IntegerMultBounds.MathlibTM2.StackCompileInvariant

/-! Transfer the family loop's proved resource certificate to selected-size
compiled stock. The certificate is produced by familyComplexBatchLoop_spec. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedFamilyBatchLoop_compiled_volume_le {Q A : ℕ} {P U : Type} [Fintype P]
    (body : P → Pr P 263 Q A U) (main : P) (ct : ℕ) (recovery : Bool)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (hmain : body main = countedLoop 240 (familyComplexBatchStep recovery hR hQ)) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ u target a b : ℕ,
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      ∀ (s t : Store (HΓ (T := 263) A) (HS 263 Q A U)) (steps outputStock : ℕ),
      (∀ C, mnProgPush (familyComplexBatchStep (P := P) (U := U) (A := A) recovery hR hQ) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize s+outputStock+depth+
          (C+1)*familyComplexBatchStepCost A (Sizes.p n) u
            (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) (Sizes.t n i) a b target)
          depth (countedLoop 240 (familyComplexBatchStep recovery hR hQ)) s steps t) →
      ReachWithin (mcode body main)
        (fun c => compiledSize body c ≤ mnSize s+outputStock+1+Sizes.T n)
        (cfg (some .entry) s none []) (steps+2) (cfg none t none []) := by
  let C := max (mnProgPush (familyComplexBatchStep (P := P) (U := U) (A := A) recovery hR hQ))
    (mnPushC body)
  filter_upwards [selectedFamilyBatchStepCost_scaled_volume_le ct (C+1)] with n hn
  intro h i _ u target a b hu htarget hband ha hb s t steps outputStock htrace
  have hcost := hn h i A u target a b hu htarget hband ha hb
  have ht := htrace C (le_max_left _ _)
    (fun f => (mn_progPush_le_pushC body f).trans (le_max_right _ _)) 1
  have hw : ExecWithin body (fun d z => mnSize z+d ≤ mnSize s+outputStock+1+Sizes.T n)
      1 (body main) s steps t := by
    rw [hmain]
    exact ht.mono (fun _ _ hz => hz.trans (Nat.add_le_add_left hcost _))
  exact hw.stock_run_main

end IntegerMultBounds.MathlibTM2.Cost
