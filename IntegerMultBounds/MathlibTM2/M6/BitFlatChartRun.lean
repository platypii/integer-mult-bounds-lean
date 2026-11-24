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

/-- The head pair runs after the tail, matching composition of the port machines. -/
def digitSwapPermutation {d : ℕ} (pairs : List {p : Fin d × Fin d // p.1 < p.2}) : Equiv.Perm (Fin d) :=
  pairs.foldr (fun p π => π * Equiv.swap p.val.1 p.val.2) 1

theorem exists_digitSwapPairs {d : ℕ} (π : Equiv.Perm (Fin d)) :
    ∃ pairs, digitSwapPermutation pairs = π := by
  induction π using Equiv.Perm.swap_induction_on' with
  | one => exact ⟨[],rfl⟩
  | mul_swap π i j ne ih =>
    obtain ⟨pairs,rfl⟩ := ih
    by_cases lt : i < j
    · exact ⟨⟨(i,j),lt⟩ :: pairs,rfl⟩
    · refine ⟨⟨(j,i),lt_of_le_of_ne (le_of_not_gt lt) ne.symm⟩ :: pairs,?_⟩
      exact congrArg (digitSwapPermutation pairs * ·) (Equiv.swap_comm j i)

noncomputable def digitSwapSkeleton {d : ℕ} (machine : {p : Fin d × Fin d // p.1 < p.2} → SharedBankSkeleton.Skeleton 1 prime)
    (pairs : List {p : Fin d × Fin d // p.1 < p.2}) : SharedBankSkeleton.Skeleton 1 prime :=
  pairs.foldr (fun p rest => SharedBankSkeleton.compose rest (machine p))
    (SharedBankSkeleton.identity 1 prime (by decide))

/-- Physical subbank for an occurrence in a compiled permutation. Each
composition prepends one shared owner slot before its two child banks. -/
noncomputable def digitSwapBank {d : ℕ}
    (machine : {p : Fin d × Fin d // p.1 < p.2} → SharedBankSkeleton.Skeleton 1 prime)
    (pairs : List {p : Fin d × Fin d // p.1 < p.2}) (a : Fin pairs.length) :
    Fin (machine pairs[a]).tapes ↪ Fin (digitSwapSkeleton machine pairs).tapes :=
  match pairs, a with
  | [], a => Fin.elim0 a
  | p :: ps, a => Fin.cases (Fin.natAddEmb (1+(digitSwapSkeleton machine ps).tapes))
      (fun b => ((digitSwapBank machine ps b).trans (Fin.natAddEmb 1)).trans (Fin.castAddEmb (machine p).tapes)) a

theorem digitSwapBank_disjoint {d : ℕ}
    (machine : {p : Fin d × Fin d // p.1 < p.2} → SharedBankSkeleton.Skeleton 1 prime)
    (pairs : List {p : Fin d × Fin d // p.1 < p.2}) :
    ∀ a b : Fin pairs.length, a ≠ b → ∀ h l, digitSwapBank machine pairs a h ≠ digitSwapBank machine pairs b l := by
  induction pairs with
  | nil => exact fun a => Fin.elim0 a
  | cons p ps ih =>
    have apart (a : Fin ps.length) (h : Fin (machine p).tapes) (l : Fin (machine ps[a]).tapes) :
        digitSwapBank machine (p :: ps) 0 h ≠ digitSwapBank machine (p :: ps) a.succ l := by
      intro eq
      have val := congrArg Fin.val eq
      change 1+(digitSwapSkeleton machine ps).tapes+h.val = 1+(digitSwapBank machine ps a l).val at val
      have := (digitSwapBank machine ps a l).isLt
      omega
    intro a b ne
    induction a using Fin.cases with
    | zero =>
      induction b using Fin.cases with
      | zero => exact False.elim (ne rfl)
      | succ b => exact apart b
    | succ a =>
      induction b using Fin.cases with
      | zero => exact fun h l => (apart a l h).symm
      | succ b =>
        let place := (Fin.natAddEmb 1 (m := (digitSwapSkeleton machine ps).tapes)).trans (Fin.castAddEmb (machine p).tapes)
        exact fun h l => place.injective.ne (ih a b (fun eq => ne (congrArg Fin.succ eq)) h l)

/-- Compile the supplied stages themselves, retaining each occurrence's
private tape contents in the composite machine. -/
noncomputable def digitSwapStage {d V : ℕ}
    (stage : {p : Fin d × Fin d // p.1 < p.2} → SharedBankStage.Stage _ 1 prime (@portOwner V))
    (pairs : List {p : Fin d × Fin d // p.1 < p.2}) :=
  pairs.foldr (fun p rest => SharedBankStage.compose rest (stage p))
    (SharedBankStage.identity _ (by decide))

theorem digitSwapStage_run {d w W : ℕ}
    (stage : {p : Fin d × Fin d // p.1 < p.2} →
      SharedBankStage.Stage _ 1 prime (@portOwner ((prime^w)^d*W)))
    (price : ℕ) (cost : ∀ p, (stage p).cost = price)
    (read : ∀ p x (a : Fin d → ZMod (prime^w)) (j : Fin W), (stage p).transform x
      (FlatCoordinateLayout.index (a ∘ Equiv.swap p.val.1 p.val.2) j) =
      x (FlatCoordinateLayout.index a j))
    (pairs : List {p : Fin d × Fin d // p.1 < p.2}) :
    SharedBankSkeleton.ofStage (digitSwapStage stage pairs) =
        digitSwapSkeleton (fun p => SharedBankSkeleton.ofStage (stage p)) pairs ∧
      (digitSwapStage stage pairs).cost = pairs.length*(price+1) ∧
      ∀ x a j, (digitSwapStage stage pairs).transform x
        (FlatCoordinateLayout.index (a ∘ digitSwapPermutation pairs) j) =
        x (FlatCoordinateLayout.index a j) := by
  induction pairs with
  | nil => exact ⟨rfl,(Nat.zero_mul _).symm,fun _ _ _ => rfl⟩
  | cons p ps ih =>
    obtain ⟨fixed,paid,action⟩ := ih
    refine ⟨?_,?_,?_⟩
    · exact (SharedBankSkeleton.ofStage_compose _ _).trans
        (congrArg (fun m => SharedBankSkeleton.compose m _) fixed)
    · change (digitSwapStage stage ps).cost + (stage p).cost + 1 = (ps.length+1)*(price+1)
      rw [paid,cost]; ring
    · intro x a j
      exact (read p ((digitSwapStage stage ps).transform x) (a ∘ digitSwapPermutation ps) j).trans
        (action x a j)

/-- Use the same list for the machine, its swap bill and its address permutation. -/
theorem digitPerm_from_pairs {d : ℕ} (pairs : List {p : Fin d × Fin d // p.1 < p.2})
    (price : ℕ → ℕ → ℕ) (swaps : DigitSwapCost d price) :
    ∃ machine : {p : Fin d × Fin d // p.1 < p.2} → SharedBankSkeleton.Skeleton 1 prime, ∀ w W, 0 < w → 0 < W →
      let V := (prime^w)^d*W
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
        SharedBankSkeleton.ofStage stage = digitSwapSkeleton machine pairs ∧ stage.cost = pairs.length*(price w W+1) ∧
        HasStackSeed stage.metadata ∧ ∀ x a j,
          stage.transform x (FlatCoordinateLayout.index (a ∘ digitSwapPermutation pairs) j) =
            x (FlatCoordinateLayout.index a j) := by
  classical
  choose machine build using fun p : {p : Fin d × Fin d // p.1 < p.2} => swaps p.val.1 p.val.2 p.property
  refine ⟨machine,?_⟩
  intro w W hw hW V
  choose stage fixed cost seed read using fun p => build p w W hw hW
  obtain ⟨skeleton,paid,action⟩ := digitSwapStage_run stage _ cost read pairs
  refine ⟨digitSwapStage stage pairs,?_,paid,?_,action⟩
  · exact skeleton.trans (congrArg (fun m => digitSwapSkeleton m pairs) (funext fixed))
  · clear skeleton paid action
    induction pairs with
    | nil => exact HasStackSeed.empty 1
    | cons p ps ih => exact compose_seed ih (seed p)

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
  obtain ⟨pairs,rfl⟩ := exists_digitSwapPairs π
  obtain ⟨machine,run⟩ := digitPerm_from_pairs pairs price swaps
  exact ⟨pairs.length,digitSwapSkeleton machine pairs,run⟩

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
