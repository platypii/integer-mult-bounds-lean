module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedRawHeaderVolume
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRawCallerStockCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedBatchStepTrace
public import IntegerMultBounds.MathlibTM2.StackCompileInvariant

/-! The derived-width raw caller's whole stock allowance fits below box volume. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedFamilyInverseCallerStock_scaled_volume_le (ct scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ A u target : ℕ, u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      scale*familyInverseCallerStockCost A (inverseCallerWordWidth p u l target s t)
        p u l target s t ≤ Sizes.T n := by
  filter_upwards [selectedRawHeaderCost_scaled_volume_le ct (3*scale),
    selectedFamilyAllKeysSetup_scaled_volume_le ct (3*scale),
    selectedFamilyBatchStepCost_scaled_volume_le ct (21*scale)] with n hnHeader hnSetup hnStep
  intro h i _ A u target hu htarget hband
  dsimp only
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let l := haloInverseRingLog s t
  let W := inverseCallerWordWidth p u l target s t
  let header := inverseScalarAtoms p s t u 0 s*tblC W 0+
    inverseMasterCopyCost W (inverseMasterValues p u l target s t 0 s)+
    inverseReleaseCost W (inverseMasterValues p u l target s t 0 s)
  let setup := generatedFamilyComplexSetupCostBound A p u l s t 0 s target
  let K := familyComplexBatchStepCost A p u l s t 0 s target
  let key : SelectedFamilyKey n i ct :=
    (⟨u,by omega⟩,⟨target,by omega⟩,⟨0,by omega⟩,⟨s,by dsimp only [s]; omega⟩)
  have hkey : selectedFamilyKeySetupCost n i ct A key = setup := by
    simp only [selectedFamilyKeySetupCost,key,if_pos hband]
    rfl
  have hsingle : selectedFamilyKeySetupCost n i ct A key ≤
      ∑ k : SelectedFamilyKey n i ct, selectedFamilyKeySetupCost n i ct A k :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ key)
  rw [hkey] at hsingle
  have hs : 3*scale*setup ≤ Sizes.T n :=
    (Nat.mul_le_mul_left (3*scale) hsingle).trans (hnSetup h i A)
  have hh : 3*scale*header ≤ Sizes.T n := hnHeader h i u target hu htarget hband
  have hk : 21*scale*K ≤ Sizes.T n :=
    hnStep h i A u target 0 s hu htarget hband (Nat.zero_le _) le_rfl
  have hc : familyInverseCallerStockCost A W p u l target s t ≤ header+setup+7*K :=
    familyInverseCallerStockCost_le (h.good.lt i) A W p u l target
  have hscaled := Nat.mul_le_mul_left scale hc
  nlinarith only [hscaled,hh,hs,hk]

/-- The resource certificate constructed by the raw numerical caller holds at
all compiled configurations, including scalar installation and final erasure. -/
theorem selectedFamilyInverseCaller_compiled_volume_le {Q A : ℕ} {P U : Type} [Fintype P]
    (body : P → Pr P 303 Q A U) (main : P) (ct : ℕ) (recovery : Bool)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (hmain : body main = familyInverseCaller recovery hR hQ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ u target : ℕ, u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let W := inverseCallerWordWidth p u l target s t
      ∀ (S R : Store (HΓ (T := 303) A) (HS 303 Q A U)) (steps : ℕ),
      (∀ C, mnProgPush (familyInverseCaller (P := P) (U := U) (A := A) recovery hR hQ) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize S+depth+
          (C+1)*familyInverseCallerStockCost A W p u l target s t)
          depth (familyInverseCaller recovery hR hQ) S steps R) →
      ReachWithin (mcode body main) (fun c => compiledSize body c ≤ mnSize S+1+Sizes.T n)
        (cfg (some .entry) S none []) (steps+2) (cfg none R none []) := by
  let C := max (mnProgPush (familyInverseCaller (P := P) (U := U) (A := A) recovery hR hQ))
    (mnPushC body)
  filter_upwards [selectedFamilyInverseCallerStock_scaled_volume_le ct (C+1)] with n hn
  intro h i _ u target hu htarget hband
  dsimp only
  intro S R steps htrace
  have hc := hn h i A u target hu htarget hband
  have ht := htrace C (le_max_left _ _)
    (fun f => (mn_progPush_le_pushC body f).trans (le_max_right _ _)) 1
  have hw : ExecWithin body (fun d z => mnSize z+d ≤ mnSize S+1+Sizes.T n)
      1 (body main) S steps R := by
    rw [hmain]
    exact ht.mono (fun _ _ hz => hz.trans (Nat.add_le_add_left hc _))
  exact hw.stock_run_main

end IntegerMultBounds.MathlibTM2.Cost
