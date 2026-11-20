module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackWeightedLeafRun
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodParentSetup
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.RevBudget

/-! Charge weighted leaves at their actual terminal widths and volumes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine RecursiveInterchangeLayout M8.RevMachine
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable def weightedLeafRate [M8.Machine.Net] (tapes push : ℕ) (L : ℝ) : ℝ :=
  (1+186*(push : ℝ))*((3*(210*(2*((prime.size : ℝ)+1)^2)+16120+100)+387)+
    2*(|LeafCore.C| * L*((tapes : ℝ)+5)))+(12000*(1+186*(push : ℝ))+125+550)

theorem weightedLeafCost_le [M8.Machine.Net] (N width tapes push : ℕ) {L : ℝ}
    (widthBound : ((max 1 width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau ≤ L) :
    (weightedLeafCost N width tapes push : ℝ) ≤ weightedLeafRate tapes push L*N := by
  have core := RevBudget.coreCost_le N width widthBound
  unfold weightedLeafCost weightedLeafBodyCost weightedLeafRate
  push_cast
  calc
    _ ≤ (1+186*(push : ℝ))*((3*(210*(2*((prime.size : ℝ)+1)^2)+16120+100)+387)*N+
        2*((|LeafCore.C| * N*L)*((tapes : ℝ)+5)))+(12000*(1+186*(push : ℝ))+125)*N + 550*N := by gcongr
    _ = _ := by ring

/-- The packed leaf pays the archive charge from a single radix factor.
The terminal recurrence can use its usual descriptor volume. -/
theorem packedWeightedLeafCost_le [M8.Machine.Net] (v : Descriptor) (positive : v.Positive)
    (tapes push rate : ℕ) {L : ℝ}
    (widthBound : ((max 1 v.width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau ≤ L) :
    ((weightedLeafCost (volume prime v) v.width tapes push + rate*prime^v.width : ℕ) : ℝ) ≤
      (weightedLeafRate tapes push L+rate)*volume prime v := by
  have qpos := IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos
  have pre := Nat.mul_pos (Nat.mul_pos positive.1 positive.2.1) positive.2.2.1
  have radix : prime^v.width ≤ volume prime v :=
    (Nat.le_mul_of_pos_left _ pre).trans ((Nat.le_mul_of_pos_right _ positive.2.2.2.1).trans
      ((Nat.le_mul_of_pos_right _ (pow_pos qpos _)).trans (Nat.le_mul_of_pos_right _ positive.2.2.2.2)))
  rw [Nat.cast_add,add_mul]
  exact add_le_add (weightedLeafCost_le _ _ _ _ widthBound) (by exact_mod_cast Nat.mul_le_mul_left rate radix)

/-- Successive good records retain the parent's volume. Their linear overheads
add, and the terminal interchange pays for the width left after all gaps. -/
private theorem chainCost_of_terminal {ι : Type*} (gap overhead : ι → ℕ)
    (time : List ι → Descriptor → ℕ)
    (step : ∀ i is v, gap i ≤ v.width → time (i :: is) v ≤
      time is (rankDescriptor prime (v.width-gap i) (gap i) v) + overhead i * volume prime v)
    (records : List ι) (v : Descriptor) (fits : (records.map gap).sum ≤ v.width)
    (rate : ℝ) :
    let child := rankDescriptor prime (v.width-(records.map gap).sum) (records.map gap).sum v
    (time [] child : ℝ) ≤ rate*volume prime child →
    (time records v : ℝ) ≤ (rate+(records.map overhead).sum)*(volume prime v : ℝ) := by
  intro child terminal
  have same : volume prime child = volume prime v := rankDescriptor_volume v (Nat.sub_add_cancel fits).symm
  have chain := rankDescriptor_chain_time gap overhead time step records v fits
  calc
    (time records v : ℝ) ≤ ((time [] child + (records.map overhead).sum * volume prime v : ℕ) : ℝ) :=
      Nat.cast_le.mpr chain
    _ ≤ _ := by
      push_cast
      rw [add_mul]
      apply add_le_add_left
      rw [← same]
      exact terminal

theorem weightedLeaf_chain_cost [M8.Machine.Net] {ι : Type*} (gap overhead : ι → ℕ)
    (time : List ι → Descriptor → ℕ)
    (step : ∀ i is v, gap i ≤ v.width → time (i :: is) v ≤
      time is (rankDescriptor prime (v.width-gap i) (gap i) v) + overhead i * volume prime v)
    (records : List ι) (v : Descriptor) (fits : (records.map gap).sum ≤ v.width)
    (tapes push : ℕ) (L : ℝ) :
    let child := rankDescriptor prime (v.width-(records.map gap).sum) (records.map gap).sum v
    time [] child ≤ weightedLeafCost (volume prime child) child.width tapes push →
    ((max 1 child.width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau ≤ L →
    (time records v : ℝ) ≤ (weightedLeafRate tapes push L+(records.map overhead).sum)*(volume prime v : ℝ) := by
  intro child terminal widthBound
  exact chainCost_of_terminal gap overhead time step records v fits _
    ((Nat.cast_le.mpr terminal).trans (weightedLeafCost_le _ _ _ _ widthBound))

/-- A good record reads the same active coordinate from both archives.
The rank bounds both offsets, uniformly in the coordinate and terminal width. -/
theorem packedWeightedLeaf_chain_cost [M8.Machine.Net] {ι : Type*} (gap overhead : ι → ℕ)
    (time : List ι → Descriptor → ℕ)
    (step : ∀ i is v, gap i ≤ v.width → time (i :: is) v ≤
      time is (rankDescriptor prime (v.width-gap i) (gap i) v) + overhead i * volume prime v)
    (records : List ι) (v : Descriptor) (fits : (records.map gap).sum ≤ v.width)
    (positive : v.Positive) {rank : ℕ} (i : Fin rank) (tapes push : ℕ) (L : ℝ) :
    let child := rankDescriptor prime (v.width-(records.map gap).sum) (records.map gap).sum v
    let factor := 2*(prime.size+1)^2
    let rate := (1000*(prime+1)+16*(rank-1))*factor
    time [] child ≤ weightedLeafCost (volume prime child) child.width tapes push+
      ((1000*(prime+1)+8*(i.val+i.val))*factor)*prime^child.width →
    ((max 1 child.width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau ≤ L →
    (time records v : ℝ) ≤ (weightedLeafRate tapes push L+rate+(records.map overhead).sum)*
      (volume prime v : ℝ) := by
  intro child factor rate terminal widthBound
  have power := pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos (records.map gap).sum
  have childPos : child.Positive := ⟨positive.1,positive.2.1,positive.2.2.1,
    Nat.mul_pos (Nat.mul_pos power positive.2.2.2.1) power,positive.2.2.2.2⟩
  have indexBound : 8*(i.val+i.val) ≤ 16*(rank-1) := by have := i.isLt; omega
  have bounded := terminal.trans (Nat.add_le_add_left (Nat.mul_le_mul_right (prime^child.width)
    (Nat.mul_le_mul_right factor (Nat.add_le_add_left indexBound _))) _)
  exact chainCost_of_terminal gap overhead time step records v fits _
    ((Nat.cast_le.mpr bounded).trans (packedWeightedLeafCost_le child childPos tapes push rate widthBound))

/-- For a rank-one terminal child the quotient atom has the full remaining
width. Both packed archive indices are zero. Price the incoming word, child
setup, packed leaf and outgoing word together on the parent descriptor. -/
theorem rankOneRecordLeaf_cost [M8.Machine.Net] {T A : ℕ} {U : Type}
    (machine : Fin 55 ↪ Fin T) (g digits tapes push : ℕ) :
    ∃ overhead : ℕ, ∀ (v : Descriptor) w (L : ℝ), v.Positive → v.width = (1+g)*(w+1) →
      let child := rankDescriptor prime (w+1) (g*(w+1)) v
      let M := prime^(w+1)
      let H := Nat.size M
      let W := v.beforeRows*v.rows*v.beforeH*v.between*v.afterD
      let K := digits*H+1
      let budget := weightedLeafCost (volume prime child) child.width tapes push+
        (1000*(prime+1)*(2*(prime.size+1)^2))*M
      let middle := (((List.finRange 1).map fun i => childWeightTime prime w H i.val).sum+1+
        dimensionTime H K (g+g))+(budget+2+(2*(1*H+1*H+((g+g)*H+K))+7))
      ((max 1 child.width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau ≤ L →
      ((1+goodIncomingTime (P := Empty) (U := U) (A := A) Empty.elim machine prime w W H W.size 1
        (Nat.le_add_right 1 g)+middle+(1+goodOutgoingTime (P := Empty) (U := U) (A := A) Empty.elim
          machine prime w W H W.size 1 (Nat.le_add_right 1 g)) : ℕ) : ℝ) ≤
        (weightedLeafRate tapes push L+overhead)*volume prime v := by
  obtain ⟨c,adapter⟩ := goodRecordTime_volume_le (P := Empty) (U := U) (A := A) Empty.elim machine
    1 g digits rfl (by omega) (Nat.le_add_right 1 g)
  let rate := 1000*(prime+1)*(2*(prime.size+1)^2)
  refine ⟨rate+c,?_⟩
  intro v w L pos split child M H W K budget middle widthBound
  have hW : 0 < W := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos pos.1 pos.2.1)
    pos.2.2.1) pos.2.2.2.1) pos.2.2.2.2
  have same : volume prime child = volume prime v := rankDescriptor_volume v (by rw [split,Nat.add_mul,one_mul])
  have wordVolume : M^((1+g)+(1+g))*W = volume prime v := by
    simp only [volume,split,M,W,pow_add]; ring
  have power := pow_pos Networks.Shared50ModularControl.prime_prime.pos (g*(w+1))
  have childPos : child.Positive := ⟨pos.1,pos.2.1,pos.2.2.1,Nat.mul_pos (Nat.mul_pos power pos.2.2.2.1) power,pos.2.2.2.2⟩
  have leaf := packedWeightedLeafCost_le child childPos tapes push rate widthBound
  change (budget : ℝ) ≤ _ at leaf
  rw [same] at leaf
  have parent := adapter w W budget hW
  change _ ≤ budget+c*(M^((1+g)+(1+g))*W) at parent
  rw [wordVolume] at parent
  apply (Nat.cast_le.mpr parent).trans
  push_cast
  linarith only [leaf]

/-- Every coordinate call sees the full payload volume at one atom's width.
Charge the packed archive scans at their actual indices and the empty
instruction ending the sequence once. -/
theorem weightedCoordinates_cost [M8.Machine.Net] {r : ℕ} (v : Descriptor) (width : v.width = r)
    (w tapes push : ℕ) :
    let M := prime^(w+1)
    let view := fun i : Fin r => {(RecursiveInterchangeLayout.child M 1 1 v i i.rev) with width := w+1}
    let factor := 2*(prime.size+1)^2
    let cost := fun i : Fin r => weightedLeafCost (volume prime (view i)) (w+1) tapes push+
      ((1000*(prime+1)+8*(i.val+i.val))*factor)*M
    ((List.finRange r).map cost).sum+1 ≤
      r*(weightedLeafCost (volume M v) (w+1) tapes push+
        ((1000*(prime+1)+16*(r-1))*factor)*M)+1 := by
  intro M view factor cost
  let bound := weightedLeafCost (volume M v) (w+1) tapes push+((1000*(prime+1)+16*(r-1))*factor)*M
  have each (i : Fin r) : cost i ≤ bound := by
    have same := RecursiveInterchangeLayout.child_volume_div M 1 1 v i i.rev
      (by simpa using width) (by decide) (one_dvd _)
    have vol : volume prime (view i) = volume M v := by
      simpa [view,M,volume,RecursiveInterchangeLayout.child] using same
    have indexBound : 8*(i.val+i.val) ≤ 16*(r-1) := by have := i.isLt; omega
    dsimp only [cost,bound]
    rw [vol]
    gcongr
  have total (is : List (Fin r)) : (is.map cost).sum ≤ is.length*bound := by
    induction is with
    | nil => simp
    | cons i is ih =>
      simpa only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul,Nat.add_comm] using
        Nat.add_le_add (each i) ih
  simpa only [List.length_finRange] using Nat.add_le_add_right (total (List.finRange r)) 1

end IntegerMultBounds.MathlibTM2.Cover.Fallback
