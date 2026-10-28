module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedFamilyStockCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedRawBatchKeys
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedBatchStepTrace
public import IntegerMultBounds.MathlibTM2.StackCompileInvariant

/-! The raw caller has linear batch stock plus one box-volume scratch allowance,
including scalar headers, every compiled configuration and final erasure. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedRawFamilyBatch_compiled_volume_le {Q A : ℕ} {P U : Type} [Fintype P]
    (body : P → Pr P 303 Q A U) (main : P) (ct : ℕ) (recovery : Bool)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (hmain : body main = familyInverseBatchCaller recovery hR hQ) :
    ∃ D : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ u target a b : ℕ,
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
        (haloBoundary s t (PhaseCellBand.width p u) a b).card
      let w := executionWidth p l (initialSchurTarget p u bits 2) 2
      ∀ (S R : Store (HΓ (T := 303) A) (HS 303 Q A U)) (steps replicas : ℕ),
      (∀ C, mnProgPush (familyInverseBatchCaller (P := P) (U := U) (A := A) recovery hR hQ) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize S+depth+
          (C+1)*familyInverseBatchCallerStockCost A (inverseCallerWordWidth p u l target s t) p u l s t a b target replicas)
          depth (familyInverseBatchCaller recovery hR hQ) S steps R) →
      ReachWithin (mcode body main)
        (fun c => compiledSize body c ≤ mnSize S+D*replicas*s*w+1+Sizes.T n)
        (cfg (some .entry) S none []) (steps+2) (cfg none R none []) := by
  let C := max (mnProgPush (familyInverseBatchCaller (P := P) (U := U) (A := A) recovery hR hQ))
    (mnPushC body)
  refine ⟨36*(C+1),?_⟩
  filter_upwards [selectedFamilyAllKeysSetup_scaled_volume_le ct (3*(C+1)),
    selectedFamilyAllKeysHeaders_scaled_volume_le ct (3*(C+1)),
    selectedFamilyBatchStepCost_scaled_volume_le ct (3*(C+1))] with n hnSetup hnHeaders hnStep
  intro h i _ u target a b hu htarget hband ha hb
  dsimp only
  intro S R steps replicas htrace
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let l := haloInverseRingLog s t
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
    (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let K := familyComplexBatchStepCost A p u l s t a b target
  let setup := generatedFamilyComplexSetupCostBound A p u l s t a b target
  let key : SelectedFamilyKey n i ct :=
    (⟨u,by omega⟩,⟨target,by omega⟩,⟨a,by omega⟩,⟨b,by omega⟩)
  have hkey : selectedFamilyKeySetupCost n i ct A key = setup := by
    simp only [selectedFamilyKeySetupCost,key,ite_eq_left hband]
    rfl
  have hsingle : selectedFamilyKeySetupCost n i ct A key ≤
      ∑ k : SelectedFamilyKey n i ct, selectedFamilyKeySetupCost n i ct A k :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ key)
  rw [hkey] at hsingle
  have hsetup := (Nat.mul_le_mul_left (3*(C+1)) hsingle).trans (hnSetup h i A)
  have hstep := hnStep h i A u target a b hu htarget hband ha hb
  let headers := selectedFamilyKeyHeaderCost n i ct key
  have hheaderSingle : selectedFamilyKeyHeaderCost n i ct key ≤
      ∑ k : SelectedFamilyKey n i ct, selectedFamilyKeyHeaderCost n i ct k :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ key)
  have hheaders := (Nat.mul_le_mul_left (3*(C+1)) hheaderSingle).trans (hnHeaders h i)
  have hboth : (C+1)*(headers+setup+K) ≤ Sizes.T n := by nlinarith only [hheaders,hsetup,hstep]
  have hstock : familyInverseBatchCallerStockCost A (inverseCallerWordWidth p u l target s t)
      p u l s t a b target replicas ≤ headers+setup+K+36*replicas*s*w := by
    have hc : generatedClosedFamilyComplexBatchStockCost A p u l s t a b target replicas ≤
        setup+K+36*replicas*s*w :=
      generatedClosedFamilyComplexBatchStockCost_le (h.good.lt i) A p u l a b target replicas
    have hh : headers = inverseScalarAtoms p s t u a b*TableVM.tblC (inverseCallerWordWidth p u l target s t) 0+
        inverseMasterCopyCost (inverseCallerWordWidth p u l target s t) (inverseMasterValues p u l target s t a b)+
        inverseReleaseCost (inverseCallerWordWidth p u l target s t) (inverseMasterValues p u l target s t a b) := by
      simp only [headers,selectedFamilyKeyHeaderCost,key,ite_eq_left hband]
      rfl
    calc
      _ = headers+generatedClosedFamilyComplexBatchStockCost A p u l s t a b target replicas := by
        rw [hh]
        unfold familyInverseBatchCallerStockCost
        ac_rfl
      _ ≤ headers+(setup+K+36*replicas*s*w) := Nat.add_le_add_left hc _
      _ = headers+setup+K+36*replicas*s*w := by ring
  have hbudget : (C+1)*familyInverseBatchCallerStockCost A (inverseCallerWordWidth p u l target s t) p u l s t a b target replicas ≤
      (36*(C+1))*replicas*s*w+Sizes.T n := by
    calc
      _ ≤ (C+1)*(headers+setup+K+36*replicas*s*w) := Nat.mul_le_mul_left _ hstock
      _ = (36*(C+1))*replicas*s*w+(C+1)*(headers+setup+K) := by ring
      _ ≤ _ := Nat.add_le_add_left hboth _
  have ht := htrace C (le_max_left _ _)
    (fun f => (mn_progPush_le_pushC body f).trans (le_max_right _ _)) 1
  have hw : ExecWithin body (fun d z => mnSize z+d ≤
      mnSize S+(36*(C+1))*replicas*s*w+1+Sizes.T n) 1 (body main) S steps R := by
    rw [hmain]
    apply ht.mono
    intro d z hz
    change mnSize z+d ≤ mnSize S+1+
      (C+1)*familyInverseBatchCallerStockCost A (inverseCallerWordWidth p u l target s t) p u l s t a b target replicas at hz
    omega
  exact hw.stock_run_main

end IntegerMultBounds.MathlibTM2.Cost
