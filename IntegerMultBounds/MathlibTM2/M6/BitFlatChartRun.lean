module

public import IntegerMultBounds.MathlibTM2.M6.BitChartFactors
public import IntegerMultBounds.MathlibTM2.M6.BitPortRun
import Mathlib.GroupTheory.Perm.Sign

/-! Route a bounded rational chart on a single flat owner at fixed tape width. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)
open M8.RevMachine
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Each digit transposition has a fixed tape program at the given price. -/
def DigitSwapCost (d : ℕ) (price : ℕ → ℕ → ℕ) : Prop :=
  ∀ i j : Fin d, i < j →
      ∃ machine : SharedBankSkeleton.Skeleton 1 prime, ∀ w W, 0 < w → 0 < W →
        let V := (prime^w)^d*W
        ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
          SharedBankSkeleton.ofStage stage = machine ∧ stage.cost = price w W ∧ HasStackSeed stage.metadata ∧
          ∀ x a k, stage.transform x (FlatCoordinateLayout.index (a ∘ Equiv.swap i j) k) =
            x (FlatCoordinateLayout.index a k)

theorem digitPerm_from_swaps {d : ℕ} (π : Equiv.Perm (Fin d))
    (price : ℕ → ℕ → ℕ)
    (swaps : DigitSwapCost d price) :
    ∃ (k : ℕ) (machine : SharedBankSkeleton.Skeleton 1 prime), ∀ w W, 0 < w → 0 < W →
      let V := (prime^w)^d*W
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
        SharedBankSkeleton.ofStage stage = machine ∧
        stage.cost = k*(price w W + 1) ∧ HasStackSeed stage.metadata ∧
        ∀ x a j, stage.transform x (FlatCoordinateLayout.index (a ∘ π) j) =
          x (FlatCoordinateLayout.index a j) := by
  induction π using Equiv.Perm.swap_induction_on' with
  | one =>
    refine ⟨0,SharedBankSkeleton.identity 1 prime (by decide),?_⟩
    intro w W hw hW V
    exact ⟨SharedBankStage.identity _ (by decide),rfl,(Nat.zero_mul _).symm,HasStackSeed.empty 1,fun _ _ _ => rfl⟩
  | mul_swap π i j ne ih =>
    obtain ⟨k,m,run⟩ := ih
    wlog lt : i < j generalizing i j
    · rw [Equiv.swap_comm i j]
      exact this j i ne.symm (lt_of_le_of_ne (le_of_not_gt lt) ne.symm)
    obtain ⟨s,swap⟩ := swaps i j lt
    refine ⟨k+1,SharedBankSkeleton.compose m s,?_⟩
    intro w W hw hW V
    obtain ⟨A,fa,ca,sa,ra⟩ := run w W hw hW
    obtain ⟨B,fb,cb,sb,rb⟩ := swap w W hw hW
    refine ⟨SharedBankStage.compose A B,?_,?_,compose_seed sa sb,?_⟩
    · simp only [SharedBankSkeleton.ofStage_compose,fa,fb]
    · change A.cost+B.cost+1 = _
      rw [ca,cb]; ring
    · intro x a j
      exact (rb (A.transform x) (a ∘ π) j).trans (ra x a j)

open Matrix IntegerMultBounds.Swap.Modular in
/-- For fixed chart data, both the tape program and number of digit swaps
are independent of precision and spectator count. -/
theorem flatChart_from_swaps {d : ℕ} (U : Matrix (Fin d) (Fin d) ℚ) (unit : IsUnit U)
    (pos : 1 ≤ d) (size : d ≤ 529)
    (entries : ∀ i j, (U i j).num.natAbs ≤ 10^10000 ∧ (U i j).den ≤ 10^10000)
    (price : ℕ → ℕ → ℕ)
    (swaps : DigitSwapCost d price) :
    ∃ (c k : ℕ) (machine : SharedBankSkeleton.Skeleton 1 prime), ∀ w W, 0 < w → 0 < W →
      let V := (prime^w)^d*W
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
        SharedBankSkeleton.ofStage stage = machine ∧
        stage.cost = c*V + k*(price w W + 1) + 2 ∧
        HasStackSeed stage.metadata ∧ ∀ x a j,
          stage.transform x (FlatCoordinateLayout.index (reduce (prime^w) U *ᵥ a) j) =
            x (FlatCoordinateLayout.index a j) := by
  obtain ⟨A,B,π,factors,action⟩ := chartFactors U unit pos size entries
  have left := factors A (by simp)
  have right := factors B (by simp)
  obtain ⟨ca,ma,ra⟩ := triangularPort_owner A left.1 left.2 false
  obtain ⟨cb,mb,rb⟩ := triangularPort_owner B right.1 right.2 false
  obtain ⟨k,mp,rp⟩ := digitPerm_from_swaps π price swaps
  refine ⟨ca+cb,k,SharedBankSkeleton.compose (SharedBankSkeleton.compose mb mp) ma,?_⟩
  intro w W hw hW V
  obtain ⟨a,fa,ta,sa,readA⟩ := ra w W hW
  obtain ⟨b,fb,tb,sb,readB⟩ := rb w W hW
  obtain ⟨p,fp,tp,sp,readP⟩ := rp w W hw hW
  refine ⟨SharedBankStage.compose (SharedBankStage.compose b p) a,?_,?_,compose_seed (compose_seed sb sp) sa,?_⟩
  · simp only [SharedBankSkeleton.ofStage_compose,fa,fb,fp]
  · change b.cost+p.cost+1+a.cost+1 = _
    rw [ta,tb,tp]; ring
  · intro x v j
    rw [action]
    exact (readA _ _ j).trans ((readP _ _ j).trans (readB x v j))

open Matrix IntegerMultBounds.Swap.Modular in
theorem flatChart_owner [M8.Machine.Net] {d : ℕ} (U : Matrix (Fin d) (Fin d) ℚ) (unit : IsUnit U)
    (pos : 1 ≤ d) (size : d ≤ 529)
    (entries : ∀ i j, (U i j).num.natAbs ≤ 10^10000 ∧ (U i j).den ≤ 10^10000) :
    ∃ (c k : ℕ) (machine : SharedBankSkeleton.Skeleton 1 prime), ∀ w W, 0 < w → 0 < W →
      let V := (prime^w)^d*W
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
        SharedBankSkeleton.ofStage stage = machine ∧
        stage.cost = c*V + k*(3808274*V + LeafCore.coreCost V w + 1) + 2 ∧
        HasStackSeed stage.metadata ∧ ∀ x a j,
          stage.transform x (FlatCoordinateLayout.index (reduce (prime^w) U *ᵥ a) j) =
            x (FlatCoordinateLayout.index a j) := by
  exact flatChart_from_swaps U unit pos size entries
    (fun w W => 3808274*((prime^w)^d*W) + LeafCore.coreCost ((prime^w)^d*W) w) digitSwap_owner

open Matrix IntegerMultBounds.Swap.Modular in
/-- Recover flat addresses after a chart change by undoing its three factors. -/
theorem flatChartReturn_from_swaps {d : ℕ} (U : Matrix (Fin d) (Fin d) ℚ) (unit : IsUnit U)
    (pos : 1 ≤ d) (size : d ≤ 529)
    (entries : ∀ i j, (U i j).num.natAbs ≤ 10^10000 ∧ (U i j).den ≤ 10^10000)
    (price : ℕ → ℕ → ℕ) (swaps : DigitSwapCost d price) :
    ∃ (c k : ℕ) (machine : SharedBankSkeleton.Skeleton 1 prime), ∀ w W, 0 < w → 0 < W →
      let V := (prime^w)^d*W
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
        SharedBankSkeleton.ofStage stage = machine ∧
        stage.cost = c*V + k*(price w W + 1) + 2 ∧
        HasStackSeed stage.metadata ∧ ∀ x a j,
          stage.transform x (FlatCoordinateLayout.index a j) =
            x (FlatCoordinateLayout.index (reduce (prime^w) U *ᵥ a) j) := by
  obtain ⟨A,B,π,factors,action⟩ := chartFactors U unit pos size entries
  have left := factors A (by simp)
  have right := factors B (by simp)
  obtain ⟨ca,ma,ra⟩ := triangularPort_owner A left.1 left.2 true
  obtain ⟨cb,mb,rb⟩ := triangularPort_owner B right.1 right.2 true
  obtain ⟨k,mp,rp⟩ := digitPerm_from_swaps π.symm price swaps
  refine ⟨ca+cb,k,SharedBankSkeleton.compose (SharedBankSkeleton.compose ma mp) mb,?_⟩
  intro w W hw hW V
  obtain ⟨a,fa,ta,sa,readA⟩ := ra w W hW
  obtain ⟨b,fb,tb,sb,readB⟩ := rb w W hW
  obtain ⟨p,fp,tp,sp,readP⟩ := rp w W hw hW
  refine ⟨SharedBankStage.compose (SharedBankStage.compose a p) b,?_,?_,compose_seed (compose_seed sa sp) sb,?_⟩
  · simp only [SharedBankSkeleton.ofStage_compose,fa,fb,fp]
  · change a.cost+p.cost+1+b.cost+1 = _
    rw [ta,tb,tp]; ring
  · intro x v j
    rw [action]
    let M := reduce (prime^w) B
    let y := M *ᵥ v
    let z := y ∘ π
    have undo (E : Matrix (Fin d) (Fin d) (ZMod (prime^w))) (unit : IsUnit E) (u : Fin d → _) :
        E⁻¹ *ᵥ (E *ᵥ u) = u := by rw [mulVec_mulVec,nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp unit),one_mulVec]
    have rA := readA x (reduce (prime^w) A *ᵥ z) j
    have rP := readP (a.transform x) z j
    have rB := readB (p.transform (a.transform x)) y j
    simp only [ite_true,undo _ (left.2 w).2] at rA
    simp only [ite_true,y,M,undo _ (right.2 w).2] at rB
    have cancel : z ∘ π.symm = y := by funext i; exact congrArg y (π.apply_symm_apply i)
    rw [cancel] at rP
    exact rB.trans (rP.trans rA)

open Matrix IntegerMultBounds.Swap.Modular in
theorem flatChartReturn_owner [M8.Machine.Net] {d : ℕ} (U : Matrix (Fin d) (Fin d) ℚ) (unit : IsUnit U)
    (pos : 1 ≤ d) (size : d ≤ 529)
    (entries : ∀ i j, (U i j).num.natAbs ≤ 10^10000 ∧ (U i j).den ≤ 10^10000) :
    ∃ (c k : ℕ) (machine : SharedBankSkeleton.Skeleton 1 prime), ∀ w W, 0 < w → 0 < W →
      let V := (prime^w)^d*W
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
        SharedBankSkeleton.ofStage stage = machine ∧
        stage.cost = c*V + k*(3808274*V + LeafCore.coreCost V w + 1) + 2 ∧
        HasStackSeed stage.metadata ∧ ∀ x a j,
          stage.transform x (FlatCoordinateLayout.index a j) =
            x (FlatCoordinateLayout.index (reduce (prime^w) U *ᵥ a) j) := by
  exact flatChartReturn_from_swaps U unit pos size entries
    (fun w W => 3808274*((prime^w)^d*W) + LeafCore.coreCost ((prime^w)^d*W) w) digitSwap_owner

/-- Reading a moved word uses the image address going forward and the preimage
address on return. -/
def routedCell {α β : Type*} (backward : Bool) (x y : α → β) (src dst : α) : Prop :=
  if backward then y src = x dst else y dst = x src

open Matrix IntegerMultBounds.Swap.Modular in
theorem flatChartDirection_from_swaps {d : ℕ} (U : Matrix (Fin d) (Fin d) ℚ) (unit : IsUnit U)
    (pos : 1 ≤ d) (size : d ≤ 529)
    (entries : ∀ i j, (U i j).num.natAbs ≤ 10^10000 ∧ (U i j).den ≤ 10^10000) (backward : Bool)
    (price : ℕ → ℕ → ℕ) (swaps : DigitSwapCost d price) :
    ∃ (c k : ℕ) (machine : SharedBankSkeleton.Skeleton 1 prime), ∀ w W, 0 < w → 0 < W →
      let V := (prime^w)^d*W
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
        SharedBankSkeleton.ofStage stage = machine ∧
        stage.cost = c*V + k*(price w W + 1) + 2 ∧
        HasStackSeed stage.metadata ∧ ∀ x a j,
          routedCell backward x (stage.transform x) (FlatCoordinateLayout.index a j)
            (FlatCoordinateLayout.index (reduce (prime^w) U *ᵥ a) j) := by
  cases backward with
  | false => exact flatChart_from_swaps U unit pos size entries price swaps
  | true => exact flatChartReturn_from_swaps U unit pos size entries price swaps

open Matrix IntegerMultBounds.Swap.Modular in
theorem flatChartDirection_owner [M8.Machine.Net] {d : ℕ} (U : Matrix (Fin d) (Fin d) ℚ) (unit : IsUnit U)
    (pos : 1 ≤ d) (size : d ≤ 529)
    (entries : ∀ i j, (U i j).num.natAbs ≤ 10^10000 ∧ (U i j).den ≤ 10^10000) (backward : Bool) :
    ∃ (c k : ℕ) (machine : SharedBankSkeleton.Skeleton 1 prime), ∀ w W, 0 < w → 0 < W →
      let V := (prime^w)^d*W
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
        SharedBankSkeleton.ofStage stage = machine ∧
        stage.cost = c*V + k*(3808274*V + LeafCore.coreCost V w + 1) + 2 ∧
        HasStackSeed stage.metadata ∧ ∀ x a j,
          routedCell backward x (stage.transform x) (FlatCoordinateLayout.index a j)
            (FlatCoordinateLayout.index (reduce (prime^w) U *ᵥ a) j) := by
  exact flatChartDirection_from_swaps U unit pos size entries backward
    (fun w W => 3808274*((prime^w)^d*W) + LeafCore.coreCost ((prime^w)^d*W) w) digitSwap_owner

end IntegerMultBounds.MathlibTM2.M6.BitNode
