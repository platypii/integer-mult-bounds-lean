module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryChildCost
public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryDirectoryOutgoing
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOrdinaryCost
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodParentSetup

/-! Cost of the generated outgoing ordinary row at the selected parent width. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host
open Shared50ModularControl (prime)

def outgoingScanRowCost (m w prefixLength tapes push base : ℕ) (active live : Bool) : ℕ :=
  let cursor := 1+(4*prefixLength+4+(m*m*(4*(w+1)+4)+1)+1)
  (if active then base+(4*tapes+1+tapes*(6*(push*base)))+cursor else cursor) + (if live then 4 else 3)

theorem outgoingRowTime_volume [M8.Machine.Net] (U : Type) {T : ℕ} (bank : Fin 55 ↪ Fin T)
    (r g : ℕ) (dim : r+g = 64) :
    ∃ C : ℝ, ∀ w W width, 0 < W →
      let M := prime^(w+1)
      let V := M^128*W
      width ≤ V → (outgoingRowTime U bank r g w W width : ℝ) ≤
        C*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau*V := by
  obtain ⟨setup,setupBound⟩ := ordinaryRowTime_volume_le 64 0 (by decide)
  obtain ⟨parent,parentBound⟩ := goodRecordTime_volume_le (A := prime) (P := Empty) (U := U)
    Empty.elim bank r g 0 rfl (by omega) (Nat.le_add_right r g)
  obtain ⟨child,childBound⟩ := ordinaryChildOverhead_le U
  let fixed := 12*64*64+4+setup+parent
  refine ⟨(fixed : ℝ)+child,?_⟩
  intro w W width positive M V fits
  let H := M.size
  let route := ((ordinaryChildPackSchedule r g).map (fun i =>
    completeSwapTime (P := Empty) (U := U) Empty.elim 128 i (i+1) w W H W.size)).sum+1
  let correction := ordinaryCorrectionTime U w W H W.size
  let weights := ((List.finRange r).map fun i => childWeightTime prime w H i.val).sum+1
  let exit := goodOutgoingTime (A := prime) (P := Empty) (U := U) Empty.elim bank prime w W H W.size r (Nat.le_add_right r g)
  have prep := setupBound r w W width 0 (by omega) positive
  simp only [ordinaryRowTime,Nat.zero_mul,Nat.zero_add,Nat.add_zero] at prep
  have header : ordinarySetupTime 64 r w H width ≤ (12*64*64+4+setup)*V := by
    rw [Nat.add_mul]
    exact ((Nat.le_add_right _ _).trans prep).trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ fits) _)
  have outer := parentBound w W 0 positive
  have parentCost : weights+(1+exit) ≤ parent*V := by
    change 1+_+(weights+_+_)+(1+exit) ≤ 0+parent*(M^((r+g)+(r+g))*W) at outer
    rw [show M^((r+g)+(r+g))*W = V by rw [dim]] at outer
    omega
  let power := ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau
  have childCost : ((2*(1+route)+correction : ℕ) : ℝ) ≤ child*power*V := by
    have h := childBound ⟨r,by omega⟩ w W positive
    simpa only [show 64-r = g by omega,route,correction,ordinaryCorrectionTime,H,M,V,power] using h
  have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast Nat.le_add_left 1 w)
    M8.Machine.BudgetBound.exponent_range.1.le
  have bill : outgoingRowTime U bank r g w W width ≤ fixed*V+(2*(1+route)+correction) := by
    change ordinarySetupTime (r+g) r w H width + (weights+(1+_+correction)+(1+exit)) ≤ _
    rw [dim]
    change ordinarySetupTime 64 r w H width + (weights+(1+route+correction)+(1+exit)) ≤ _
    dsimp only [fixed]
    rw [Nat.add_mul]
    omega
  calc
    _ ≤ ((fixed*V+(2*(1+route)+correction) : ℕ) : ℝ) := by exact_mod_cast bill
    _ ≤ (fixed : ℝ)*power*V+child*power*V := by
      rw [Nat.cast_add,Nat.cast_mul]
      exact add_le_add (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (Nat.cast_nonneg _) one) (Nat.cast_nonneg V)) childCost
    _ = _ := by dsimp only [power]; ring

/-- Include clearing the local tapes, advancing the directory and dispatching
both selectors. The rate is uniform in the precision and the spectator width. -/
theorem outgoingScanRowCost_volume [M8.Machine.Net] (U : Type) {T : ℕ} (bank : Fin 55 ↪ Fin T)
    (r g tapes push : ℕ) (dim : r+g = 64) :
    ∃ C : ℝ, ∀ w W width, 0 < W →
      let M := prime^(w+1)
      let V := M^128*W
      ∀ active live, width ≤ V →
      (outgoingScanRowCost 64 w width tapes push (outgoingRowTime U bank r g w W width) active live : ℝ) ≤
        C*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau*V := by
  obtain ⟨C,row⟩ := outgoingRowTime_volume U bank r g dim
  let factor := 1+6*tapes*push
  let overhead := 4*tapes+32785
  refine ⟨(factor : ℝ)*C+overhead,?_⟩
  intro w W width hW M V active live fits
  let base := outgoingRowTime U bank r g w W width
  let power := ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau
  have pos : 0 < M := pow_pos Shared50ModularControl.prime_prime.pos _
  have ticks : w+1 ≤ V :=
    (Nat.le_of_lt (Nat.lt_pow_self Shared50ModularControl.prime_prime.one_lt)).trans
      ((show M ≤ M^128 by simpa using Nat.pow_le_pow_right pos (by decide : 1 ≤ 128)).trans
        (Nat.le_mul_of_pos_right _ hW))
  have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast Nat.le_add_left 1 w)
    M8.Machine.BudgetBound.exponent_range.1.le
  have fixed : 4*tapes ≤ 4*tapes*V := Nat.le_mul_of_pos_right _ (by omega)
  have price : outgoingScanRowCost 64 w width tapes push base active live ≤ factor*base+overhead*V := by
    have scale : factor*base = base+tapes*(6*(push*base)) := by dsimp [factor]; ring
    rw [scale]
    dsimp only [overhead,outgoingScanRowCost]
    rw [Nat.add_mul]
    cases active <;> cases live <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
  calc
    _ ≤ ((factor*base+overhead*V : ℕ) : ℝ) := by exact_mod_cast price
    _ ≤ (factor : ℝ)*(C*power*V)+(overhead : ℝ)*power*V := by
      push_cast
      exact add_le_add (mul_le_mul_of_nonneg_left (row w W width hW fits) (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (Nat.cast_nonneg _) one) (Nat.cast_nonneg _))
    _ = _ := by dsimp only [power]; ring

/-- Sum the physical outgoing row bills and include the packed queue motion. -/
theorem outgoingDirectoryTime_volume [M8.Machine.Net] (U : Type) {T : ℕ} (bank : Fin 55 ↪ Fin T)
    (r g tapes push : ℕ) (dim : r+g = 64) :
    ∃ C : ℝ, ∀ w W, 0 < W →
      let M := prime^(w+1)
      let V := M^128*W
      ∀ (rs : List ℕ) (width : ℕ → ℕ) (active live : ℕ → Bool),
      (∀ j ∈ rs, width j ≤ V) →
      let cost := fun j => outgoingScanRowCost (r+g) w (width j) tapes push
        (outgoingRowTime U bank r g w W (width j)) (active j) (live j)
      (((rs.map cost).sum+12*(rs.length*V)+12*rs.length+4 : ℕ) : ℝ) ≤
        C*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau*(rs.length*V)+4 := by
  obtain ⟨C,row⟩ := outgoingScanRowCost_volume U bank r g tapes push dim
  refine ⟨C+24,?_⟩
  intro w W positive M V rs width active live fits cost
  let power := ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau
  have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast Nat.le_add_left 1 w)
    M8.Machine.BudgetBound.exponent_range.1.le
  have sum : ∀ xs : List ℕ, (∀ j ∈ xs, width j ≤ V) →
      ((xs.map cost).sum : ℝ) ≤ (xs.length : ℝ)*(C*power*V) := by
    intro xs bounded
    induction xs with
    | nil => simp
    | cons j xs ih =>
      have h := row w W (width j) positive (active j) (live j) (bounded j List.mem_cons_self)
      have head : (cost j : ℝ) ≤ C*power*V := by simpa only [cost,dim] using h
      have both := add_le_add head (ih (fun i hi => bounded i (List.mem_cons_of_mem _ hi)))
      simpa [add_mul,add_comm] using both
  have volume : rs.length ≤ rs.length*V :=
    Nat.le_mul_of_pos_right _ (Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) positive)
  have count : (rs.length : ℝ) ≤ rs.length*(V : ℝ) := by exact_mod_cast volume
  have paid := mul_le_mul_of_nonneg_right one (show 0 ≤ (rs.length : ℝ)*V by positivity)
  have total := sum rs fits
  change _ ≤ (C+24)*power*((rs.length : ℝ)*V)+4
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  nlinarith only [total,count,paid]

end IntegerMultBounds.MathlibTM2.M6.BitNode
