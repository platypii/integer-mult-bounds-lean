module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.NodeCall
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.FamilyControlBounds
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.CounterCostBounds

/-! Actual call entry has linear active-volume workspace. Shared counter
estimates keep the proof independent of the whole recursive time budget. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.NodeCall
open IntegerMultBounds IntegerMultBounds.Machine Networks
  Networks.Shared50ModularControl RecursiveInterchangeLayout FlatCoordinateSchedule
  CommonBank Routines SharedBankStageInput RecursiveRoleSerialization NodeBank
noncomputable section

theorem countersCost_linear (r f m V : ℕ) (hf : f ≤ V) (hV : 1 ≤ V) (hr : r ≤ m) :
    countersCost r f m ≤ (2*(m+1)*(2*m+57)+40)*V := by
  have ha := RevBudget.advs_le hf hV (show r-1+1 ≤ m+1 by omega)
  have hb := RevBudget.advs_le hf hV (show m-r-1+1 ≤ m+1 by omega)
  have hl := RevBudget.bits_len f
  have hl' := RevBudget.bits_len (f-1)
  have h : countersCost r f m ≤ 2*((m+1)*((2*m+57)*V))+40*V := by
    unfold countersCost
    omega
  exact h.trans_eq (by ring)

def enterSpaceConstant (N : RevNetwork) (k : ℕ) : ℕ :=
  88*tapes N+54000+2*(N.width+1)*(2*N.width+57)+k

theorem enterCost_linear (N : RevNetwork) (w : N.World ⊕ N.Temp) (k : ℕ)
    (v : Descriptor) (hv : v.Positive) (b f r : ℕ) (hb : 0 < b)
    (hw : v.width = (N.width*f)*b) (hr : r ≤ N.width) :
    enterCost (N := N) w f r k (volume prime v) ≤ enterSpaceConstant N k*volume prime v := by
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hv
  have hsquare := Family.width_square_le_volume v hv
  have hwV : v.width ≤ volume prime v := by nlinarith only [hsquare]
  have hmf : N.width*f ≤ volume prime v :=
    (by rw [hw] at hwV; exact (Nat.le_mul_of_pos_right _ hb).trans hwV)
  have hf : f ≤ volume prime v := (Nat.le_mul_of_pos_left _ (by have := N.two_le_width; omega)).trans hmf
  have hcc := countersCost_linear r f N.width (volume prime v) hf hV hr
  have hlen (x : ℕ) (hx : x ≤ volume prime v) : (bits x).length ≤ 2*volume prime v := by
    have h := RevBudget.bits_len x
    omega
  have hleft := hlen ((N.width-r)*f) ((Nat.mul_le_mul_right f (Nat.sub_le _ _)).trans hmf)
  have hright := hlen (r*f) ((Nat.mul_le_mul_right f hr).trans hmf)
  have hpark := NodePark.parked_length_le N w
  have hpay := Nat.mul_le_mul_right (volume prime v)
    (show 88*(NodePark.parked N w).length+51883 ≤ 88*tapes N+51883 by omega)
  have hk := Nat.le_mul_of_pos_right k hV
  have hz : (bits 0).length = 0 := rfl
  unfold enterCost enterSpaceConstant
  rw [hz]
  nlinarith only [hcc,hleft,hright,hpay,hk,hV]

theorem recCountersCost_linear (N : RevNetwork) (v : Descriptor) (hv : v.Positive) (b f : ℕ)
    (hb : 0 < b) (hf : 0 < f) (hw : v.width = (N.width*f)*b) :
    recCountersCost b f N.width ≤
      (4100+BinaryDescriptorDivMod.linearConstant (bits N.width))*volume prime v := by
  have hm : 1 ≤ N.width := by have h := N.two_le_width; omega
  have hn : 1 ≤ N.width*f := Nat.mul_pos hm hf
  have hp := Family.prepCost_linear v hv b N.width (N.width*f) hb hn hw
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hv
  have hsquare := Family.width_square_le_volume v hv
  have hmf : N.width*f ≤ volume prime v := by
    have h := Nat.le_mul_of_pos_right (N.width*f) hb
    rw [←hw] at h
    exact h.trans (by nlinarith only [hsquare])
  have hfV : f ≤ volume prime v := (Nat.le_mul_of_pos_left _ hm).trans hmf
  have hl := RevBudget.bits_len (N.width*f)
  have hz : (bits 0).length = 0 := rfl
  unfold recCountersCost
  unfold Family.prepCost at hp
  rw [hz]
  nlinarith only [hp,hV,hmf,hfV,hl]

def recoverSpaceConstant (N : RevNetwork) : ℕ :=
  92*tapes N+56200+BinaryDescriptorDivMod.linearConstant (bits N.width)

theorem recoverCost_linear (N : RevNetwork) (w : N.World ⊕ N.Temp)
    (v : Descriptor) (hv : v.Positive) (b f r : ℕ) (hb : 0 < b) (hf : 0 < f)
    (hw : v.width = (N.width*f)*b) (hr : r ≤ N.width) :
    recoverCost (N := N) w (hdr v) (hdr (childView (N := N) b f r v)) b f (volume prime v) ≤
      recoverSpaceConstant N*volume prime v := by
  have hsc : 0+r*f ≤ N.width*f := by simpa using Nat.mul_le_mul_right f hr
  have he : (N.width-r)*f = N.width*f-0-r*f := by rw [Nat.sub_mul]; omega
  have hrestore := Enter.restore_cost_le (q := prime) Shared50ModularControl.prime_prime.two_le hv
    (n := N.width*f) (w := b) (s := 0) (c := r*f) (e := (N.width-r)*f) hw hsc he (hdr_headers v)
  rw [hdr_eq (Headers.child_headers (hdr_headers v) he)] at hrestore
  have hc := recCountersCost_linear N v hv b f hb hf hw
  have hpark := NodePark.parked_length_le N w
  have hpay := Nat.mul_le_mul_right (volume prime v)
    (show 92*(NodePark.parked N w).length+51883 ≤ 92*tapes N+51883 by omega)
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hv
  unfold recoverCost recoverSpaceConstant childView
  nlinarith only [hrestore,hc,hpay,hV]

/-- Every reachable instruction of the actual entry block has a linear-volume
head allowance, including parked payload and generated child metadata. -/
theorem enter_heads (N : RevNetwork) (w : N.World ⊕ N.Temp) {k : ℕ}
    (code : FiniteReturnStack.Code k) (v : Descriptor) (hv : v.Positive) (b f r : ℕ)
    (hb : 0 < b) (hf : 0 < f) (hw : v.width = (N.width*f)*b) (hr : 1 ≤ r) (hrm : r < N.width)
    (data : RecursiveMixedSchedule.Data (tapes N) v) (hio : data (io N) = fun _ => blank)
    (fs : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    {c : Config (enterB N w r code).tapes (enterB N w r code).states prime}
    (hc : RunInvariant (enterB N w r code).program
      (· = raw (bank (roles data) (hdr v) fs p node scalar (nodeC N b f) st) (enterB N w r code).tapes) c) :
    ∀ i,
      (raw (bank (roles data) (hdr v) fs p node scalar (nodeC N b f) st) (enterB N w r code).tapes).head i-
        (enterSpaceConstant N k*volume prime v : ℕ) ≤ c.head i ∧
      c.head i ≤ (raw (bank (roles data) (hdr v) fs p node scalar (nodeC N b f) st) (enterB N w r code).tapes).head i+
        (enterSpaceConstant N k*volume prime v : ℕ) := by
  have h := enter_runs (fs := fs) (p := p) (node := node) (scalar := scalar) (st := st)
    (N := N) w code hv hb hf hw hr hrm data hio
  have h' := h.consequence (fun _ h => h) (fun _ h => h) (enterCost_linear N w k v hv b f r hb hw hrm.le)
  exact hc.heads_eq h'

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.NodeCall
