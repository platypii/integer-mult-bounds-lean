module

public import IntegerMultBounds.MathlibTM2.M6.BitActiveChartRun
public import IntegerMultBounds.MathlibTM2.M6.BitSweepOwnerSchedule

/-! Compile the costed sweep charts on the shared permanent owner tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)
open M8.RevMachine
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

private theorem placePort_fixed {k v w : ℕ} (dst : Fin (k+1))
    (a : SharedBankStage.Stage _ 1 prime (@portOwner v))
    (b : SharedBankStage.Stage _ 1 prime (@portOwner w))
    (fixed : SharedBankSkeleton.ofStage a = SharedBankSkeleton.ofStage b) :
    SharedBankSkeleton.ofStage (placePort dst a) = SharedBankSkeleton.ofStage (placePort dst b) := by
  cases a
  cases b
  injection fixed with ht hs hp hslot
  subst_vars
  rfl

/-- A width-independent bank program moves every role to or from the sweep
layout. Each execution preserves the extra owner and admits a private stack seed. -/
private theorem sweepChartList [M8.Machine.Net] (roles : List Role) (unique : roles.Nodup) :
    ∃ C : ℝ, ∀ (n : Fin 9) (backward : Bool),
      ∃ machine : SharedBankSkeleton.Skeleton 142081 prime, ∀ (w W : ℕ), 0 < w → 0 < W →
      let V := (prime^w)^128*W
      ∃ stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        SharedBankSkeleton.ofStage stage = machine ∧ (∃ S, ChartPrivateReady stage S) ∧
        (stage.cost : ℝ) ≤ C*V*(w : ℝ)^M8.Machine.BudgetBound.tau ∧
        (∀ x r, r ∈ roles → ∀ i, routedCell backward (x (sweepRoleTape r)) (stage.transform x (sweepRoleTape r))
          i ((flatToSweep w W n r i).cast (by simpa only [Nat.one_mul] using ordinaryCompact_width (prime^w) W))) ∧
        ∀ x j, (∀ r ∈ roles, sweepRoleTape r ≠ j) → stage.transform x j = x j := by
  classical
  choose scans swaps machine port fixed paid seed read using
    fun (n : Fin 9) (backward : Bool) (r : Role) => sweepChart_owner n r backward
  let rate := fun (p : Fin 9 × Bool) (r : Role) =>
    (scans p.1 p.2 r : ℝ) + swaps p.1 p.2 r * (3808275 + |LeafCore.C|) + 3
  obtain ⟨C,bound⟩ := Finite.exists_le fun p => (roles.map (rate p)).sum
  refine ⟨C,?_⟩
  intro n backward
  let bank (w W : ℕ) (hw : 0 < w) (hW : 0 < W) := SharedBankStage.compile _ (Nat.zero_lt_succ 142080)
    (roles.map fun r => placePort (sweepRoleTape r) (port n backward r w W hw hW))
  refine ⟨SharedBankSkeleton.ofStage (bank 1 1 (by decide) (by decide)),?_⟩
  intro w W hw hW V
  let stage := bank w W hw hW
  obtain ⟨_,_,cost,cell,frame⟩ := compiledPorts_spec sweepRoleTape (fun r => port n backward r w W hw hW) roles unique
  refine ⟨stage,?_,compiledPortSeed _ _ _ (fun r _ => seed n backward r w W hw hW),?_,?_,?_⟩
  · simp only [stage,bank,SharedBankSkeleton.ofStage_compile,List.map_map]
    apply congrArg (SharedBankSkeleton.compile 142081 prime _)
    apply List.map_congr_left
    intro r _
    exact placePort_fixed _ _ _ ((fixed n backward r w W hw hW).trans (fixed n backward r 1 1 (by decide) (by decide)).symm)
  · let power := (w : ℝ)^M8.Machine.BudgetBound.tau
    have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast hw : (1 : ℝ) ≤ w)
      M8.Machine.BudgetBound.exponent_range.1.le
    have vol : 0 < V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hW
    have join : 1 ≤ (V : ℝ)*power := one_le_mul_of_one_le_of_one_le (by exact_mod_cast vol) one
    have scans_le : (V : ℝ) ≤ V*power := le_mul_of_one_le_right (Nat.cast_nonneg _) one
    have core := RevBudget.coreCost_le V w (L := power) (by rw [max_eq_right hw])
    have swap_le : 3808274*(V : ℝ)+LeafCore.coreCost V w+1 ≤ (3808275+|LeafCore.C|)*(V*power) := by
      nlinarith only [scans_le,core,join]
    let bill := fun r => (port n backward r w W hw hW).cost
    have total (rs : List Role) : (((rs.map bill).sum + rs.length : ℕ) : ℝ) ≤
        (rs.map (rate (n,backward))).sum * (V*power) := by
      induction rs with
      | nil => simp
      | cons r rs ih =>
        have price := paid n backward r w W hw hW
        change bill r = scans n backward r * V + swaps n backward r * (3808274*V+LeafCore.coreCost V w+1)+2 at price
        simp only [List.map_cons,List.sum_cons,List.length_cons]
        rw [price]
        push_cast at ih ⊢
        dsimp only [rate] at ih ⊢
        nlinarith only [ih,mul_le_mul_of_nonneg_left scans_le (Nat.cast_nonneg (scans n backward r)),
          mul_le_mul_of_nonneg_left swap_le (Nat.cast_nonneg (swaps n backward r)),join]
    change ((bank w W hw hW).cost : ℝ) ≤ _
    rw [show (bank w W hw hW).cost = (roles.map bill).sum + roles.length from cost,mul_assoc]
    exact (total roles).trans (mul_le_mul_of_nonneg_right (bound (n,backward)) (by positivity))
  · intro x r hr i
    have same := cell x r hr
    exact (congrArg (fun f => routedCell backward (x (sweepRoleTape r)) f i _) same).mpr
      (read n backward r w W hw hW _ i)
  · exact frame

theorem sweepChartBank [M8.Machine.Net] :
    ∃ C : ℝ, ∀ (n : Fin 9) (backward : Bool),
      ∃ machine : SharedBankSkeleton.Skeleton 142081 prime, ∀ (w W : ℕ), 0 < w → 0 < W →
      let V := (prime^w)^128*W
      ∃ stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        SharedBankSkeleton.ofStage stage = machine ∧ (∃ S, ChartPrivateReady stage S) ∧
        (stage.cost : ℝ) ≤ C*V*(w : ℝ)^M8.Machine.BudgetBound.tau ∧
        (∀ x r i, routedCell backward (x (sweepRoleTape r)) (stage.transform x (sweepRoleTape r))
          i ((flatToSweep w W n r i).cast (by simpa only [Nat.one_mul] using ordinaryCompact_width (prime^w) W))) ∧
        ∀ x, stage.transform x (Fin.last 142080) = x (Fin.last 142080) := by
  classical
  let e := Fintype.equivFin Role
  let roles := (List.finRange (Fintype.card Role)).map e.symm
  have unique : roles.Nodup := (List.nodup_finRange _).map e.symm.injective
  have mem (r : Role) : r ∈ roles := List.mem_map.mpr ⟨e r,List.mem_finRange _,e.symm_apply_apply _⟩
  obtain ⟨C,build⟩ := sweepChartList roles unique
  refine ⟨C,?_⟩
  intro n backward
  obtain ⟨m,run⟩ := build n backward
  refine ⟨m,?_⟩
  intro w W hw hW V
  obtain ⟨stage,fixed,seed,cost,read,frame⟩ := run w W hw hW
  refine ⟨stage,fixed,seed,cost,fun x r => read x r (mem r),?_⟩
  exact fun x => frame x _ (fun r _ => Fin.castSucc_ne_last _)

/-- The charged chart stages discharge both address hypotheses of the
corrected sweep. Only its worker effect is required from the middle execution. -/
theorem correctedFlatChartBank [M8.Machine.Net] :
    ∃ C : ℝ, ∀ (n : Fin 9) (w W : ℕ), 0 < w → 0 < W →
      let M := prime^w
      let V := M^128*W
      let size : M^16*(1*(M^112*W)) = V := by simpa only [Nat.one_mul] using ordinaryCompact_width M W
      ∃ (entry exit : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)))
        (pre post : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := M^16*(1*(M^112*W))))),
        ((entry.cost+pre.cost+post.cost+exit.cost : ℕ) : ℝ) ≤ C*V*(w : ℝ)^M8.Machine.BudgetBound.tau ∧
        ∀ x y, let input := fun t i => entry.transform x t (Fin.cast size i)
          let output := exit.transform (fun t i => post.transform y t (Fin.cast size.symm i))
          sweepEffect n w 1 W (pre.transform input) y →
          ∀ j : Fin W,
            let address := fun z => FlatCoordinateLayout.index
              ((addressMod M z ∘ Equiv.sumCongr stageAxis.symm stageAxis.symm) ∘ (@finSumFinEquiv 64 64).symm) j
            readRoles address output = (Piece.stage n).run (readRoles address x) := by
  obtain ⟨C,charts⟩ := sweepChartBank
  obtain ⟨D,_,_,correct⟩ := correctedSweep_flat
  refine ⟨C+D+C,?_⟩
  intro n w W hw hW M V size
  obtain ⟨_,enter⟩ := charts n false
  obtain ⟨_,leave⟩ := charts n true
  obtain ⟨entry,_,_,before,reads,_⟩ := enter w W hw hW
  obtain ⟨exit,_,_,after,writes,_⟩ := leave w W hw hW
  obtain ⟨pre,post,_,_,_,_,middle,step⟩ := correct n w W hw hW
  refine ⟨entry,exit,pre,post,?_,?_⟩
  · change ((pre.cost+post.cost : ℕ) : ℝ) ≤ D*(w : ℝ)^M8.Machine.BudgetBound.tau*(M^16*(1*(M^112*W)) : ℕ) at middle
    conv at middle => rhs; rw [size]
    change (entry.cost : ℝ) ≤ C*V*(w : ℝ)^M8.Machine.BudgetBound.tau at before
    change (exit.cost : ℝ) ≤ C*V*(w : ℝ)^M8.Machine.BudgetBound.tau at after
    push_cast at middle ⊢
    nlinarith only [before,after,middle]
  · intro x y input output worker
    apply step x output input y worker
    · exact fun r i => reads x r i
    · intro r i
      have back := writes (fun t i => post.transform y t (Fin.cast size.symm i)) r i
      simpa only [output,sweepRoleTape_eq,routedCell,ite_true,Fin.cast_cast,Fin.cast_eq_self] using back.symm

end IntegerMultBounds.MathlibTM2.M6.BitNode
