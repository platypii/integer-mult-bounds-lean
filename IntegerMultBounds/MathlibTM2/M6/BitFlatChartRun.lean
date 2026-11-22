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

private theorem digitPerm_owner [M8.Machine.Net] {d : ℕ} (π : Equiv.Perm (Fin d)) :
    ∃ (k : ℕ) (machine : SharedBankSkeleton.Skeleton 1 prime), ∀ w W, 0 < w → 0 < W →
      let V := (prime^w)^d*W
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
        SharedBankSkeleton.ofStage stage = machine ∧
        stage.cost = k*(3808274*V + LeafCore.coreCost V w + 1) ∧ HasStackSeed stage.metadata ∧
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
    obtain ⟨s,swap⟩ := digitSwap_owner i j lt
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
  obtain ⟨A,B,π,factors,action⟩ := chartFactors U unit pos size entries
  have left := factors A (by simp)
  have right := factors B (by simp)
  obtain ⟨ca,ma,ra⟩ := triangularPort_owner A left.1 left.2 false
  obtain ⟨cb,mb,rb⟩ := triangularPort_owner B right.1 right.2 false
  obtain ⟨k,mp,rp⟩ := digitPerm_owner π
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

end IntegerMultBounds.MathlibTM2.M6.BitNode
