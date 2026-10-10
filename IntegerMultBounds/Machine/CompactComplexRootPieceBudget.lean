import IntegerMultBounds.Machine.CompactComplexRootPieceRun

/-! Root enumeration charges every queue read, numeric update and loop test
separately from the recursive callback costs. No callback runtime is treated
as an elementary transition. -/
namespace IntegerMultBounds.Machine.CompactComplexRootPieceBudget
noncomputable section
open ActiveRepairRankHeadersCommands (State put)
open CompactComplexRootPieceNumbers

/-- One generated digit pays its own physical control overhead, in addition
to the sum of the genuine recursive callback costs. -/
theorem digit_cost_le (st : State) (e left width digit base : ℕ)
    (h1 : st 1=some e) (h3 : st 3=some width) (hb : 0<base)
    (callCost : ℕ → ℕ) :
    CompactComplexRootPieceDigit.digitCost st left width digit base callCost ≤
      (∑ j ∈ Finset.range digit, callCost j)+
      digit*(1000*(left+digit*width+width+digit+1)+3)+
      1000*(e+width*base+base+1)+2*digit+112 := by
  have hbits := ActiveRepairRankHeadersCommands.bits_length digit
  have hlevel := level_cost_le (put st 2 (left+digit*width)) e width base hb
    (by simpa [put,Function.update] using h1) (by simpa [put,Function.update] using h3)
  have hpieces :
      (∑ j ∈ Finset.range digit,
        (callCost j+CompactChildHeadersArithmetic.scheduleCost piece
          (CompactComplexRootPieceClock.clock st (left+j*width) (digit-j))+3)) ≤
      (∑ j ∈ Finset.range digit, callCost j)+
        digit*(1000*(left+digit*width+width+digit+1)+3) := by
    calc
      _ ≤ ∑ j ∈ Finset.range digit,
          (callCost j+(1000*(left+digit*width+width+digit+1)+3)) := by
        apply Finset.sum_le_sum
        intro j hj
        have h := piece_cost_le
          (CompactComplexRootPieceClock.clock st (left+j*width) (digit-j))
          (left+j*width) width (digit-j)
          (by simp [CompactComplexRootPieceClock.clock,put])
          (by simp [CompactComplexRootPieceClock.clock,put,h3])
          (by simp [CompactComplexRootPieceClock.clock,put])
        have hjd : j≤digit := Nat.le_of_lt (Finset.mem_range.mp hj)
        have hmul := Nat.mul_le_mul_right width hjd
        have hsub := Nat.sub_le digit j
        omega
      _ = _ := by simp [Finset.sum_add_distrib]
  unfold CompactComplexRootPieceDigit.digitCost
  omega

private theorem overhead_le (e left width digit base A : ℕ)
    (he : e≤A) (hl : left≤A) (hw : width≤A) (hd : digit≤base) :
    digit*(1000*(left+digit*width+width+digit+1)+3)+
      1000*(e+width*base+base+1)+2*digit+112 ≤
      10000*(base+1)^2*(A+1) := by
  have hm := Nat.mul_le_mul hd hw
  have hs : left+digit*width+width+digit+1≤A+base*A+A+base+1 := by omega
  have hp := Nat.mul_le_mul hd (Nat.add_le_add_right (Nat.mul_le_mul_left 1000 hs) 3)
  have hw' := Nat.mul_le_mul_right base hw
  have hq : 1000*(e+width*base+base+1)≤1000*(A+A*base+base+1) := by omega
  have hrest :
      digit*(1000*(left+digit*width+width+digit+1)+3)+
        1000*(e+width*base+base+1)+2*digit+112 ≤
      base*(1000*(A+base*A+A+base+1)+3)+
        1000*(A+A*base+base+1)+2*base+112 :=
    Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hp hq) (Nat.mul_le_mul_left 2 hd)) 112
  exact hrest.trans (by nlinarith [Nat.zero_le (base^2*A),Nat.zero_le (base^2)])

/-- Fixed-base enumeration has only linear control overhead per queue digit,
with an explicit constant independent of all recursive callback runtimes. -/
theorem digit_cost_uniform (st : State) (e left width digit base A : ℕ)
    (h1 : st 1=some e) (h3 : st 3=some width) (hb : 0<base)
    (he : e≤A) (hl : left≤A) (hw : width≤A) (hd : digit≤base)
    (callCost : ℕ → ℕ) :
    CompactComplexRootPieceDigit.digitCost st left width digit base callCost ≤
      (∑ j ∈ Finset.range digit, callCost j)+10000*(base+1)^2*(A+1) := by
  have h := digit_cost_le st e left width digit base h1 h3 hb callCost
  have ho := overhead_le e left width digit base A he hl hw hd
  exact h.trans (by simpa only [Nat.add_assoc] using (Nat.add_le_add_left ho
    (∑ j ∈ Finset.range digit, callCost j)))

open CompactComplexRecursiveGeometry (arity)
open CompactComplexRootPieceVisits (preceding)

private theorem preceding_take_le (active k : ℕ) :
    preceding ((Nat.digits arity active).take k)≤active := by
  have hsplit := congrArg preceding (List.take_append_drop k (Nat.digits arity active))
  simp only [preceding,CompactComplexRootPieceVisits.expand_append,List.map_append,
    List.sum_append,Nat.zero_add] at hsplit
  have h := Nat.le_add_right
    (((CompactComplexRecursiveGeometry.expandDigits 0 ((Nat.digits arity active).take k)).map
      (fun j => arity^j)).sum)
    (((CompactComplexRecursiveGeometry.expandDigits ((Nat.digits arity active).take k).length
      ((Nat.digits arity active).drop k)).map (fun j => arity^j)).sum)
  rw [hsplit] at h
  exact h.trans_eq (CompactComplexRootPieceController.final_left active)

private theorem digits_length_le (active : ℕ) : (Nat.digits arity active).length≤active := by
  by_cases hz : active=0
  · subst active; simp
  rw [Nat.length_digits arity active (by decide) hz]
  exact Nat.succ_le_of_lt (Nat.log_lt_self arity hz)

/-- All root queue-digit bodies charge their real callback sums plus one
uniform quadratic overhead in the original active-axis count. -/
theorem controller_cost_le (active : ℕ) (callCost : ℕ → ℕ → ℕ) :
    (∑ k : Fin (Nat.digits arity active).length,
      (CompactComplexRootPieceController.bodyCost (CompactComplexRootDigits.state 0)
        (Nat.digits arity active) k callCost+2)) ≤
    (∑ k : Fin (Nat.digits arity active).length,
      ∑ j ∈ Finset.range (Nat.digits arity active)[k.val], callCost k.val j)+
      (10000*(arity+1)^2+2)*active*(active+1) := by
  have hbody : ∀ k : Fin (Nat.digits arity active).length,
      CompactComplexRootPieceController.bodyCost (CompactComplexRootDigits.state 0)
        (Nat.digits arity active) k callCost+2 ≤
      (∑ j ∈ Finset.range (Nat.digits arity active)[k.val], callCost k.val j)+
        (10000*(arity+1)^2+2)*(active+1) := by
    intro k
    have hk := (Nat.lt_digits_length_iff (by decide : 1<arity) active).mp k.isLt
    have he : k.val≤active := (Nat.le_of_lt k.isLt).trans (digits_length_le active)
    have hd : (Nat.digits arity active)[k.val]≤arity := Nat.le_of_lt
      (Nat.digits_lt_base (by decide : 1<arity) (List.getElem_mem k.isLt))
    have h := digit_cost_uniform
      (CompactComplexRootPieceController.state (CompactComplexRootDigits.state 0)
        (Nat.digits arity active) k.val) k.val
      (preceding ((Nat.digits arity active).take k.val)) (arity^k.val)
      (Nat.digits arity active)[k.val] arity active
      (by simp [CompactComplexRootPieceController.state,CompactComplexRootPieceController.ready,put])
      (by simp [CompactComplexRootPieceController.state,CompactComplexRootPieceController.ready,put])
      (by decide) he (preceding_take_le active k.val) hk hd (callCost k.val)
    unfold CompactComplexRootPieceController.bodyCost
    have htwo : 2≤2*(active+1) := by omega
    calc
      _ ≤ ((∑ j ∈ Finset.range (Nat.digits arity active)[k.val], callCost k.val j)+
        10000*(arity+1)^2*(active+1))+2 := Nat.add_le_add_right h 2
      _ ≤ _ := by nlinarith
  have hs := Finset.sum_le_sum (fun k (_ : k∈Finset.univ) => hbody k)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    smul_eq_mul] at hs
  have hm := Nat.mul_le_mul_right ((10000*(arity+1)^2+2)*(active+1)) (digits_length_le active)
  have hfinal := hs.trans (Nat.add_le_add_left hm
    (∑ k : Fin (Nat.digits arity active).length,
      ∑ j ∈ Finset.range (Nat.digits arity active)[k.val], callCost k.val j))
  simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    smul_eq_mul,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hfinal

private theorem fields_length_le {a : ℕ} (base : ℕ) (ds : List ℕ)
    (hd : ∀ d∈ds,d≤base) :
    (CompactComplexRootDigits.fields (a:=a) ds).length≤(base+2)*ds.length := by
  induction ds with
  | nil => simp [CompactComplexRootDigits.fields]
  | cons d ds ih =>
    have hb := ActiveRepairRankHeadersCommands.bits_length d
    have hD := hd d (by simp)
    have ht := ih (fun x hx => hd x (List.mem_cons_of_mem d hx))
    simp only [CompactComplexRootDigits.fields,List.flatMap_cons,List.length_append,
      List.length_map,List.length_cons,List.length_nil,Nat.mul_add,Nat.mul_one] at *
    omega

private theorem digits_power_le (active : ℕ) :
    arity^(Nat.digits arity active).length≤arity*(active+1) := by
  by_cases hz : active=0
  · subst active; simp [arity]
  exact (Nat.base_pow_length_digits_le arity active (by decide) hz).trans
    (Nat.mul_le_mul_left arity (Nat.le_succ active))

/-- Explicit polynomial overhead for the complete root lifecycle, including
original-header setup, all digit control, queue erasure and numeric cleanup. -/
def overhead (active : ℕ) :=
  2*active+67+101000*(active+arity+1)^2*active+
    4*(arity+2)*active+100*(2*active+arity*(active+1)+4)+
    (10000*(arity+1)^2+2)*active*(active+1)

def callbacks (active : ℕ) (callCost : ℕ → ℕ → ℕ) :=
  ∑ k : Fin (Nat.digits arity active).length,
    ∑ j ∈ Finset.range (Nat.digits arity active)[k.val],callCost k.val j

private theorem allowance_le (active : ℕ) (callCost : ℕ → ℕ → ℕ) {a : ℕ} :
    2*active+67+101000*(active+arity+1)^2*(Nat.digits arity active).length+
      4*(CompactComplexRootDigits.fields (a:=a) (Nat.digits arity active)).length+
      100*((Nat.digits arity active).length+active+arity^(Nat.digits arity active).length+4)+
      (∑ k : Fin (Nat.digits arity active).length,
        (CompactComplexRootPieceController.bodyCost (CompactComplexRootDigits.state 0)
          (Nat.digits arity active) k callCost+2)) ≤
    overhead active+callbacks active callCost := by
  have hl := digits_length_le active
  have hf := fields_length_le (a:=a) arity (Nat.digits arity active)
    (fun d hd => Nat.le_of_lt (Nat.digits_lt_base (by decide : 1<arity) hd))
  have hfl := Nat.mul_le_mul_left (arity+2) hl
  have hF := Nat.mul_le_mul_left 4 (hf.trans hfl)
  have hp := digits_power_le active
  have he := Nat.mul_le_mul_left (101000*(active+arity+1)^2) hl
  have hx : 100*((Nat.digits arity active).length+active+arity^(Nat.digits arity active).length+4)≤
      100*(2*active+arity*(active+1)+4) := by omega
  have hc := controller_cost_le active callCost
  have hsum := Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left he (2*active+67)) hF) hx) hc
  simpa only [overhead,callbacks,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_assoc] using hsum

/-- The complete fixed root machine has one explicit polynomial control
allowance plus the actual recursive callback sum. Its controller and queue
are physically erased; the final native bank is the true callback endpoint. -/
theorem runs {a t q : ℕ} (src : Fin t) (callback : Program (43+(1+t)) q a)
    (active : ℕ) (native : ℕ → Tapes t a) (callCost : ℕ → ℕ → ℕ)
    (ht : (native 0).tape src=RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits active))
    (hh : (native 0).head src=1)
    (hc : CompactComplexRootPieceRun.CallbackSpec callback active native callCost) :
    HoareTime (CompactComplexRootPieceRun.program src callback).2
      (fun v => v=CompactComplexRootPieceDigit.input CompactComplexRootDigitsFromHeader.emptyState
        (fun _ => blank) 0 (native 0))
      (fun v => v=CompactComplexRootPieceDigit.input CompactComplexRootDigitsFromHeader.emptyState
        (fun _ => blank) 0 (native (CompactComplexRootPiecePrefixes.count (Nat.digits arity active))))
      (overhead active+callbacks active callCost) :=
  (CompactComplexRootPieceRun.runs src callback active native callCost ht hh hc).consequence
    (fun _ h => h) (fun _ h => h) (allowance_le active callCost)

end
end IntegerMultBounds.Machine.CompactComplexRootPieceBudget
