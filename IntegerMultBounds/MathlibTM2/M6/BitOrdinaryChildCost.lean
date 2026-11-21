module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryChildLayout
public import IntegerMultBounds.MathlibTM2.Cover.FallbackPhysicalScanData

/-! Per-volume cost of the PR589 child layout passes and weighted correction. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover
open Shared50ModularControl (prime)

/-- The correction uses precisely the diagonal-pair part of a signed residual.
Its binary headers therefore give the same uniform per-volume swap bound. -/
theorem childCorrectionTime_le [M8.Machine.Net] (U : Type) :
    ∃ fixed swaps : ℕ, ∀ w W, 0 < W →
      let M := prime^(w+1)
      ((List.finRange 127).map (fun i => Fallback.pairScalingTime U i.succ 0 i.succ w W M.size W.size)).sum+1 ≤
        (fixed+swaps*Fallback.swapVolumeRate w)*(M^128*W) := by
  obtain ⟨fixed,swaps,bound⟩ := Fallback.exceptionalRecordTime_binary_le U 127 0 0 0
  refine ⟨fixed,swaps,?_⟩
  intro w W positive M
  have full := bound (fun _ => 0) false w W 0 positive
  simp only [Nat.mul_zero,Nat.add_zero] at full
  apply le_trans _ full
  dsimp only [Fallback.exceptionalRecordTime,Fallback.exceptionalBodyTime,Fallback.signedResidualTime,M]
  omega

-- The pair-only rate from 2ceb5476 is subsumed by ordinaryChildOverhead_le.

/-- Preparing the diagonal is linear in the binary modulus width and hence
fits in one row-volume charge even for a single spectator. -/
theorem childCorrectionSetup_volume_le (w W : ℕ) (positive : 0 < W) :
    let M := prime^(w+1)
    let H := M.size
    4*H+4+(128*(128*(8*(64*H)+14*H+22)+1)+1+(2*H+2)) + 1 + (128*128*(4*H+4)+1) ≤
      (128*(128*(8*64+14+22+8)+1)+15)*(M^128*W) := by
  intro M H
  have modulus : 0 < M := pow_pos Shared50ModularControl.prime_prime.pos _
  have digits : H ≤ M^128*W := (Nat.size_le.mpr Nat.lt_two_pow_self : M.size ≤ M).trans
    ((show M ≤ M^128 by simpa using Nat.pow_le_pow_right modulus (by decide : 1 ≤ 128)).trans
      (Nat.le_mul_of_pos_right _ positive))
  have volume : 0 < M^128*W := Nat.mul_pos (pow_pos modulus _) positive
  omega

private theorem ordinaryChildBill {route pairs prep drop fixed passes header a b rate V : ℕ}
    (positive : 0 < V) (routing : route ≤ (fixed+passes*rate)*V)
    (matrix : prep+1+drop ≤ header*V) (diagonal : pairs ≤ (a+b*rate)*V) :
    2*(1+route)+(prep+(1+pairs)+drop) ≤
      (2*(1+fixed)+header+a+(2*passes+b)*rate)*V := by
  simp only [Nat.add_mul,Nat.mul_assoc,Nat.one_mul] at routing diagonal ⊢
  nlinarith

/-- Both physical layout passes, matrix preparation, the diagonal pairs and
archive cleanup have one parent-volume rate for every PR589 rank. -/
theorem ordinaryChildOverhead_le [M8.Machine.Net] (U : Type) :
    ∃ C : ℝ, ∀ r : Fin 65, ∀ w W : ℕ, 0 < W →
      let M := prime^(w+1)
      let H := M.size
      let V := M^128*W
      let route := ((ordinaryChildPackSchedule r (64-r.val)).map (fun i =>
        Fallback.completeSwapTime (P := Empty) (U := U) Empty.elim 128 i (i+1) w W H W.size)).sum+1
      let pairs := ((List.finRange 127).map (fun i =>
        Fallback.pairScalingTime U i.succ 0 i.succ w W H W.size)).sum+1
      ((2*(1+route) + (4*H+4+(128*(128*(8*(64*H)+14*H+22)+1)+1+(2*H+2)) +
        (1+pairs) + (128*128*(4*H+4)+1)) : ℕ) : ℝ) ≤
        C*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau*V := by
  classical
  let bound (r : Fin 65) := Fallback.packTime_le (P := Empty) (U := U) Empty.elim 128
    (ordinaryChildPackSchedule r (64-r.val)) (by decide)
  let setup := fun r => (bound r).choose
  let swaps := fun r => (bound r).choose_spec.choose
  let fixed := ∑ r : Fin 65, setup r
  let passes := ∑ r : Fin 65, swaps r
  obtain ⟨a,b,pairsBound⟩ := childCorrectionTime_le U
  let header := 128*(128*(8*64+14+22+8)+1)+15
  let base := 2*(1+fixed)+header+a
  let count := 2*passes+b
  refine ⟨base+(count : ℝ)*(3808275+M8.RevMachine.LeafCore.C),?_⟩
  intro r w W hW M H V route pairs
  have vol : 0 < V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hW
  have hr : route ≤ (fixed+passes*Fallback.swapVolumeRate w)*V := by
    apply ((bound r).choose_spec.choose_spec w W hW).trans
    have hs : setup r ≤ fixed := Finset.single_le_sum (fun i _ => Nat.zero_le (setup i)) (Finset.mem_univ r)
    have hp : swaps r ≤ passes := Finset.single_le_sum (fun i _ => Nat.zero_le (swaps i)) (Finset.mem_univ r)
    exact Nat.mul_le_mul_right V (Nat.add_le_add hs (Nat.mul_le_mul_right _ hp))
  have hc := childCorrectionSetup_volume_le w W hW
  have hp := pairsBound w W hW
  let power := ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau
  have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast Nat.le_add_left 1 w)
    M8.Machine.BudgetBound.exponent_range.1.le
  have fee : ((base+count*Fallback.swapVolumeRate w : ℕ) : ℝ) ≤
      (base+(count : ℝ)*(3808275+M8.RevMachine.LeafCore.C))*power := by
    rw [Nat.cast_add,Nat.cast_mul,add_mul,mul_assoc]
    exact add_le_add (le_mul_of_one_le_right (Nat.cast_nonneg _) one)
      (mul_le_mul_of_nonneg_left (Fallback.swapVolumeRate_le w) (Nat.cast_nonneg _))
  apply le_trans _ (mul_le_mul_of_nonneg_right fee (Nat.cast_nonneg V))
  rw [← Nat.cast_mul]
  apply Nat.cast_le.mpr
  change pairs ≤ (a+b*Fallback.swapVolumeRate w)*V at hp
  change _ ≤ header*V at hc
  exact ordinaryChildBill vol hr hc hp

end IntegerMultBounds.MathlibTM2.M6.BitNode
