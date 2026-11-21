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

noncomputable def incomingRowTime [M8.Machine.Net] (U : Type) {T : ℕ} (bank : Fin 55 ↪ Fin T)
    (r g w W width : ℕ) : ℕ :=
  let m := r+g
  let H := (prime^(w+1)).size
  let route := ((ordinaryChildPackSchedule r g).map (fun i =>
    completeSwapTime (P := Empty) (U := U) Empty.elim (m+m) i (i+1) w W H W.size)).sum+1
  ordinarySetupTime m r w H width +
    (1+goodIncomingTime (A := prime) (U := U) Empty.elim bank prime w W H W.size r (Nat.le_add_right r g)+(1+route))

theorem ordinaryRowPairTime_volume [M8.Machine.Net] (U : Type) {T : ℕ} (bank : Fin 55 ↪ Fin T)
    (r g : ℕ) (dim : r+g = 64) :
    ∃ C : ℝ, ∀ w W width, 0 < W →
      let M := prime^(w+1)
      let V := M^128*W
      width ≤ V → ((incomingRowTime U bank r g w W width + outgoingRowTime U bank r g w W width : ℕ) : ℝ) ≤
        C*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau*V := by
  obtain ⟨setup,setupBound⟩ := ordinaryRowTime_volume_le 64 0 (by decide)
  obtain ⟨parent,parentBound⟩ := goodRecordTime_volume_le (A := prime) (P := Empty) (U := U)
    Empty.elim bank r g 0 rfl (by omega) (Nat.le_add_right r g)
  obtain ⟨child,childBound⟩ := ordinaryChildOverhead_le U
  let fixed := 2*(12*64*64+4+setup)+parent
  refine ⟨(fixed : ℝ)+child,?_⟩
  intro w W width positive M V fits
  let H := M.size
  let route := ((ordinaryChildPackSchedule r g).map (fun i =>
    completeSwapTime (P := Empty) (U := U) Empty.elim 128 i (i+1) w W H W.size)).sum+1
  let correction := ordinaryCorrectionTime U w W H W.size
  let weights := ((List.finRange r).map fun i => childWeightTime prime w H i.val).sum+1
  let exit := goodOutgoingTime (A := prime) (P := Empty) (U := U) Empty.elim bank prime w W H W.size r (Nat.le_add_right r g)
  let enter := goodIncomingTime (A := prime) (P := Empty) (U := U) Empty.elim bank prime w W H W.size r (Nat.le_add_right r g)
  have prep := setupBound r w W width 0 (by omega) positive
  simp only [ordinaryRowTime,Nat.zero_mul,Nat.zero_add,Nat.add_zero] at prep
  have header : ordinarySetupTime 64 r w H width ≤ (12*64*64+4+setup)*V := by
    rw [Nat.add_mul]
    exact ((Nat.le_add_right _ _).trans prep).trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ fits) _)
  have outer := parentBound w W 0 positive
  have parentCost : 1+enter+weights+(1+exit) ≤ parent*V := by
    change 1+enter+(weights+_+_)+(1+exit) ≤ 0+parent*(M^((r+g)+(r+g))*W) at outer
    rw [show M^((r+g)+(r+g))*W = V by rw [dim]] at outer
    omega
  let power := ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau
  have childCost : ((2*(1+route)+correction : ℕ) : ℝ) ≤ child*power*V := by
    have h := childBound ⟨r,by omega⟩ w W positive
    simpa only [show 64-r = g by omega,route,correction,ordinaryCorrectionTime,H,M,V,power] using h
  have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast Nat.le_add_left 1 w)
    M8.Machine.BudgetBound.exponent_range.1.le
  have bill : incomingRowTime U bank r g w W width + outgoingRowTime U bank r g w W width ≤
      fixed*V+(2*(1+route)+correction) := by
    change (ordinarySetupTime (r+g) r w H width+(1+enter+(1+_)))+
      (ordinarySetupTime (r+g) r w H width+(weights+(1+_+correction)+(1+exit))) ≤ _
    rw [dim]
    change (ordinarySetupTime 64 r w H width+(1+enter+(1+route)))+
      (ordinarySetupTime 64 r w H width+(weights+(1+route+correction)+(1+exit))) ≤ _
    dsimp only [fixed]
    rw [Nat.add_mul,Nat.mul_assoc]
    omega
  calc
    _ ≤ ((fixed*V+(2*(1+route)+correction) : ℕ) : ℝ) := by exact_mod_cast bill
    _ ≤ (fixed : ℝ)*power*V+child*power*V := by
      rw [Nat.cast_add,Nat.cast_mul]
      exact add_le_add (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (Nat.cast_nonneg _) one) (Nat.cast_nonneg V)) childCost
    _ = _ := by dsimp only [power]; ring

theorem outgoingRowTime_volume [M8.Machine.Net] (U : Type) {T : ℕ} (bank : Fin 55 ↪ Fin T)
    (r g : ℕ) (dim : r+g = 64) :
    ∃ C : ℝ, ∀ w W width, 0 < W →
      let M := prime^(w+1)
      let V := M^128*W
      width ≤ V → (outgoingRowTime U bank r g w W width : ℝ) ≤
        C*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau*V := by
  obtain ⟨C,bound⟩ := ordinaryRowPairTime_volume U bank r g dim
  refine ⟨C,fun w W width positive fits => ?_⟩
  exact (Nat.cast_le.mpr (Nat.le_add_left _ _)).trans (bound w W width positive fits)

/-- Clearing, advancing and dispatching preserve a uniform per-volume row bound. -/
private theorem scanRowCost_volume [M8.Machine.Net] (baseTime : ℕ → ℕ → ℕ → ℕ) (tapes push : ℕ)
    (C : ℝ) (row : ∀ w W width, 0 < W →
      let V := (prime^(w+1))^128*W
      width ≤ V → (baseTime w W width : ℝ) ≤ C*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau*V) :
    ∃ C : ℝ, ∀ w W width, 0 < W →
      let M := prime^(w+1)
      let V := M^128*W
      ∀ active live, width ≤ V →
      (outgoingScanRowCost 64 w width tapes push (baseTime w W width) active live : ℝ) ≤
        C*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau*V := by
  let factor := 1+6*tapes*push
  let overhead := 4*tapes+32785
  refine ⟨(factor : ℝ)*C+overhead,?_⟩
  intro w W width hW M V active live fits
  let base := baseTime w W width
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

theorem outgoingScanRowCost_volume [M8.Machine.Net] (U : Type) {T : ℕ} (bank : Fin 55 ↪ Fin T)
    (r g tapes push : ℕ) (dim : r+g = 64) :
    ∃ C : ℝ, ∀ w W width, 0 < W →
      let M := prime^(w+1)
      let V := M^128*W
      ∀ active live, width ≤ V →
      (outgoingScanRowCost 64 w width tapes push (outgoingRowTime U bank r g w W width) active live : ℝ) ≤
        C*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau*V := by
  obtain ⟨C,row⟩ := outgoingRowTime_volume U bank r g dim
  exact scanRowCost_volume (outgoingRowTime U bank r g) tapes push C row

theorem incomingScanRowCost_volume [M8.Machine.Net] (U : Type) {T : ℕ} (bank : Fin 55 ↪ Fin T)
    (r g tapes push : ℕ) (dim : r+g = 64) :
    ∃ C : ℝ, ∀ w W width, 0 < W →
      let M := prime^(w+1)
      let V := M^128*W
      ∀ active live, width ≤ V →
      (outgoingScanRowCost 64 w width tapes push (incomingRowTime U bank r g w W width) active live : ℝ) ≤
        C*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau*V := by
  obtain ⟨C,row⟩ := ordinaryRowPairTime_volume U bank r g dim
  apply scanRowCost_volume (incomingRowTime U bank r g) tapes push C
  intro w W width positive V fits
  exact (Nat.cast_le.mpr (Nat.le_add_right _ _)).trans (row w W width positive fits)

/-- The incoming scanner also discards one archived 128-by-128 matrix per row. -/
theorem incomingOrdinaryTime_volume [M8.Machine.Net] (U : Type) {T : ℕ} (bank : Fin 55 ↪ Fin T)
    (r g tapes push : ℕ) (dim : r+g = 64) :
    ∃ C : ℝ, ∀ w W width, 0 < W →
      let M := prime^(w+1)
      let V := M^128*W
      ∀ live, width ≤ V →
      ((outgoingScanRowCost 64 w width tapes push (incomingRowTime U bank r g w W width) live live +
        (128*128*(4*M.size+4)+1) : ℕ) : ℝ) ≤ C*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau*V := by
  obtain ⟨C,row⟩ := incomingScanRowCost_volume U bank r g tapes push dim
  refine ⟨C+131073,?_⟩
  intro w W width positive M V live fits
  let power := ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau
  have pos : 0 < M := pow_pos Shared50ModularControl.prime_prime.pos _
  have digits : M.size ≤ V := (Nat.size_le.mpr Nat.lt_two_pow_self : M.size ≤ M).trans
    ((show M ≤ M^128 by simpa using Nat.pow_le_pow_right pos (by decide : 1 ≤ 128)).trans
      (Nat.le_mul_of_pos_right _ positive))
  have nonzero : 0 < V := Nat.mul_pos (pow_pos pos _) positive
  have drop : 128*128*(4*M.size+4)+1 ≤ 131073*V := by omega
  have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast Nat.le_add_left 1 w)
    M8.Machine.BudgetBound.exponent_range.1.le
  have overhead : (131073 : ℝ)*V ≤ 131073*power*V :=
    mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by norm_num) one) (Nat.cast_nonneg V)
  rw [Nat.cast_add,add_mul,add_mul]
  apply add_le_add (row w W width positive live live fits)
  exact (show ((128*128*(4*M.size+4)+1 : ℕ) : ℝ) ≤ 131073*V by exact_mod_cast drop).trans overhead

private theorem directoryCost_sum (rs : List ℕ) (cost : ℕ → ℕ) (V : ℕ) (C power : ℝ)
    (positive : 0 < V) (one : 1 ≤ power) (row : ∀ j ∈ rs, (cost j : ℝ) ≤ C*power*V) :
    (((rs.map cost).sum+12*(rs.length*V)+12*rs.length+4 : ℕ) : ℝ) ≤
      (C+24)*power*((rs.length : ℝ)*V)+4 := by
  have sum : ((rs.map cost).sum : ℝ) ≤ (rs.length : ℝ)*(C*power*V) := by
    induction rs with
    | nil => simp
    | cons j xs ih =>
      have both := add_le_add (row j List.mem_cons_self) (ih (fun i hi => row i (List.mem_cons_of_mem _ hi)))
      simpa [add_mul,add_comm] using both
  have volume : rs.length ≤ rs.length*V :=
    Nat.le_mul_of_pos_right _ positive
  have count : (rs.length : ℝ) ≤ rs.length*(V : ℝ) := by exact_mod_cast volume
  have paid := mul_le_mul_of_nonneg_right one (show 0 ≤ (rs.length : ℝ)*V by positivity)
  change _ ≤ (C+24)*power*((rs.length : ℝ)*V)+4
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  nlinarith only [sum,count,paid]

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
  apply directoryCost_sum _ _ _ _ _ (Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) positive) one
  intro j hj
  simpa only [cost,dim] using row w W (width j) positive (active j) (live j) (fits j hj)

private theorem exceptionalIncomingTime_volume [M8.Machine.Net] (U : Type) (d m tapes push : ℕ) :
    ∃ C : ℝ, ∀ w W width, 0 < W →
      let M := prime^(w+1)
      let V := M^(d+1)*W
      ∀ (rows : Fin (d+1) → Fin (d+1)) neg, width ≤ V →
      ((exceptionalRecordTime U rows neg m w W M.size W.size tapes push width+4 : ℕ) : ℝ) ≤
        C*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau*V := by
  obtain ⟨fixed,swaps,rate⟩ := exceptionalRecordTime_binary_le U d m tapes push
  let scale := 3808275+M8.RevMachine.LeafCore.C
  refine ⟨((fixed+8 : ℕ) : ℝ)+(swaps : ℝ)*scale,?_⟩
  intro w W width positive M V rows neg fits
  let power := ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau
  have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast Nat.le_add_left 1 w)
    M8.Machine.BudgetBound.exponent_range.1.le
  have vol : 0 < V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) positive
  have bill := rate rows neg w W width positive
  have paid : exceptionalRecordTime U rows neg m w W M.size W.size tapes push width+4 ≤
      (fixed+8+swaps*swapVolumeRate w)*V := by
    change exceptionalRecordTime U rows neg m w W M.size W.size tapes push width ≤ (fixed+swaps*swapVolumeRate w)*V+4*width at bill
    simp only [Nat.add_mul] at bill ⊢
    omega
  have fee := add_le_add (le_mul_of_one_le_right (Nat.cast_nonneg (fixed+8)) one)
    (mul_le_mul_of_nonneg_left (swapVolumeRate_le w) (Nat.cast_nonneg swaps))
  have coeff : ((fixed+8+swaps*swapVolumeRate w : ℕ) : ℝ) ≤
      (((fixed+8 : ℕ) : ℝ)+(swaps : ℝ)*scale)*power := by
    rw [Nat.cast_add,Nat.cast_mul,add_mul,mul_assoc]
    exact fee
  exact (Nat.cast_le.mpr paid).trans (by rw [Nat.cast_mul]; exact mul_le_mul_of_nonneg_right coeff (Nat.cast_nonneg _))

/-- Uniform incoming traversal cost for the actual ordinary, padding and exceptional dispatch. -/
theorem incomingDirectoryTime_volume [M8.Machine.Net] (U : Type) {T : ℕ} (bank : Fin 55 ↪ Fin T)
    (r g d tapes push rareTapes rarePush : ℕ) (dim : r+g = 64) (fields : d+1 = 128) :
    ∃ C : ℝ, ∀ w W, 0 < W →
      let M := prime^(w+1)
      let V := M^128*W
      ∀ (rs : List ℕ) (width : ℕ → ℕ) (live bad : ℕ → Bool)
        (pivots : ℕ → Fin (d+1) → Fin (d+1)) (negative : ℕ → Bool), (∀ j ∈ rs, width j ≤ V) →
      let cost := fun j =>
        if live j && bad j then exceptionalRecordTime U (pivots j) (negative j) (r+g) w W M.size W.size rareTapes rarePush (width j)+4
        else outgoingScanRowCost (r+g) w (width j) tapes push (incomingRowTime U bank r g w W (width j)) (live j) (live j)+
          ((d+1)*(d+1)*(4*M.size+4)+1)
      (((rs.map cost).sum+12*(rs.length*V)+12*rs.length+4 : ℕ) : ℝ) ≤
        C*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau*(rs.length*V)+4 := by
  obtain ⟨ordinary,regular⟩ := incomingOrdinaryTime_volume U bank r g tapes push dim
  obtain ⟨rare,exceptional⟩ := exceptionalIncomingTime_volume U d (r+g) rareTapes rarePush
  refine ⟨max ordinary rare+24,?_⟩
  intro w W hW M V rs width live bad pivots negative fits cost
  let power := ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau
  have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast Nat.le_add_left 1 w)
    M8.Machine.BudgetBound.exponent_range.1.le
  apply directoryCost_sum _ _ _ _ _ (Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hW) one
  intro j hj
  have mono {a b : ℝ} (h : a ≤ b) : a*power*V ≤ b*power*V :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (by linarith)) (Nat.cast_nonneg _)
  dsimp only [cost]
  split
  · apply le_trans _ (mono (le_max_right ..))
    have size : M^(d+1)*W = V := by rw [fields]
    exact size ▸ exceptional w W (width j) hW (pivots j) (negative j) (size.symm ▸ fits j hj)
  · apply le_trans _ (mono (le_max_left ..))
    simpa only [dim,fields] using regular w W (width j) hW (live j) (fits j hj)

end IntegerMultBounds.MathlibTM2.M6.BitNode
