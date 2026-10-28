module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyBatchTrace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedBatchStepTrace
public import IntegerMultBounds.MathlibTM2.StackCompileInvariant

/-! The live repeated-batch wrapper uses linear stream stock and one scratch
allowance, including initialization, finish and every compiled configuration. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedFamilyBatch_compiled_volume_le {Q A : ℕ} {P U : Type} [Fintype P]
    (body : P → Pr P 263 Q A U) (main : P) (ct : ℕ) (recovery : Bool)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (hmain : body main = familyComplexBatch recovery hR hQ) :
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
      let K := familyComplexBatchStepCost A p u l s t a b target
      ∀ (S R : Store (HΓ (T := 263) A) (HS 263 Q A U)) (steps replicas : ℕ),
      (∀ C, mnProgPush (familyComplexBatch (P := P) (U := U) (A := A) recovery hR hQ) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize S+depth+
          (C+1)*familyComplexBatchStockCost s w replicas K)
          depth (familyComplexBatch recovery hR hQ) S steps R) →
      ReachWithin (mcode body main)
        (fun c => compiledSize body c ≤ mnSize S+D*replicas*s*w+1+Sizes.T n)
        (cfg (some .entry) S none []) (steps+2) (cfg none R none []) := by
  let C := max (mnProgPush (familyComplexBatch (P := P) (U := U) (A := A) recovery hR hQ))
    (mnPushC body)
  refine ⟨9*(C+1),?_⟩
  filter_upwards [selectedFamilyBatchStepCost_scaled_volume_le ct (3*(C+1))] with n hn
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
  have hs : 1 ≤ s := Nat.pos_of_ne_zero (NeZero.ne _)
  have hw : 1 ≤ w := by dsimp only [w,executionWidth]; omega
  have hK : 8*(s*w)+8 ≤ K := by dsimp only [K,familyComplexBatchStepCost,w,bits]; omega
  have hsplit := familyComplexBatchStockCost_le s w replicas K hs hw hK
  have hcost := hn h i A u target a b hu htarget hband ha hb
  have hbudget : (C+1)*familyComplexBatchStockCost s w replicas K ≤
      (9*(C+1))*replicas*s*w+Sizes.T n := by
    calc
      _ ≤ (C+1)*(9*replicas*s*w+3*K) := Nat.mul_le_mul_left _ hsplit
      _ = (9*(C+1))*replicas*s*w+(3*(C+1))*K := by ring
      _ ≤ _ := Nat.add_le_add_left hcost _
  have ht := htrace C (le_max_left _ _)
    (fun f => (mn_progPush_le_pushC body f).trans (le_max_right _ _)) 1
  have hwtrace : ExecWithin body (fun d z => mnSize z+d ≤
      mnSize S+(9*(C+1))*replicas*s*w+1+Sizes.T n) 1 (body main) S steps R := by
    rw [hmain]
    apply ht.mono
    intro d z hz
    change mnSize z+d ≤ mnSize S+1+(C+1)*familyComplexBatchStockCost s w replicas K at hz
    omega
  exact hwtrace.stock_run_main

end IntegerMultBounds.MathlibTM2.Cost
