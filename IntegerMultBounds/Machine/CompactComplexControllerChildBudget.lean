import IntegerMultBounds.Machine.CompactComplexControllerChildReturn
import IntegerMultBounds.Machine.CompactComplexChildHeadersUniform
import IntegerMultBounds.Machine.CompactNativeRoleTransferBudget

/-! The complete physical child-entry and return overhead is paid from
original geometry: descriptor frames, actual return-address bits, exponent
updates, child-header synthesis, erasure and joins are all included. -/
namespace IntegerMultBounds.Machine.CompactComplexControllerChildBudget
noncomputable section
open CompactComplexRecursiveGeometry
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactComplexControllerChildPrefix (data)
open ActivePrefixStageHeadersData (initial)
variable {s : Shape} {left k : ℕ}

def entryCost (siteCount : ℕ) (rho : Fin s.chunk) (visit : Visit s.active left (k+2))
    (hactive : s.active≤s.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (slot : Fin arity) (rows : ℕ) :=
  CompactChildHeadersStack.cost (data (CompactComplexChildHeadersData.parent rho visit hactive pair))+
    CompactComplexCallReturn.addressWidth siteCount arity+20*(k+3)+103+
    CompactChildHeadersArithmetic.scheduleCost (CompactComplexChildHeadersData.schedule slot)
      (initial (CompactComplexChildHeadersData.parent rho visit hactive pair) rows)

def returnCost (rho : Fin s.chunk) (visit : Visit s.active left (k+2))
    (hactive : s.active≤s.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (slot : Fin arity) :=
  2*((data (CompactComplexChildHeadersData.child rho visit hactive pair slot) 0).length+
    (data (CompactComplexChildHeadersData.child rho visit hactive pair slot) 1).length+
    (data (CompactComplexChildHeadersData.child rho visit hactive pair slot) 2).length)+
      CompactChildHeadersStack.cost (data (CompactComplexChildHeadersData.parent rho visit hactive pair))+
        2*(k+3)+16

theorem descriptor_lengths (v : Stage s) (hactive : s.active≤s.axes) :
    ∀ i, (data v i).length≤s.axes+1 := by
  have hf := v.widthFits
  have ha := v.activeAxes
  have hl : v.left≤s.axes := by omega
  have hr : v.right≤s.axes := by omega
  intro i
  fin_cases i <;> dsimp only [data,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  · exact (ActiveRepairRankHeadersCommands.bits_length _).trans (by omega)
  · exact (ActiveRepairRankHeadersCommands.bits_length _).trans (by omega)
  · exact (ActiveRepairRankHeadersCommands.bits_length _).trans (by omega)

theorem frame_cost (v : Stage s) (hactive : s.active≤s.axes) :
    CompactChildHeadersStack.cost (data v)≤6*(s.axes+1)+23 := by
  have h0 := descriptor_lengths v hactive 0
  have h1 := descriptor_lengths v hactive 1
  have h2 := descriptor_lengths v hactive 2
  unfold CompactChildHeadersStack.cost
  omega

theorem exponent_bound (visit : Visit s.active left (k+2)) (hactive : s.active≤s.axes) :
    k+3≤s.axes+1 := by
  have hp : k+2<arity^(k+2) := Nat.lt_pow_self (by decide : 1<arity)
  have hf := visit.fits
  omega

/-- The actual finite address width is part of the constant, not an uncharged
runtime input. The dimension bound is independent of retained role rows. -/
theorem entry_bound (siteCount : ℕ) (rho : Fin s.chunk) (visit : Visit s.active left (k+2))
    (hactive : s.active≤s.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (slot : Fin arity) (rows : ℕ) :
    entryCost siteCount rho visit hactive pair slot rows ≤
      (CompactComplexChildHeadersUniform.constant+CompactComplexCallReturn.addressWidth siteCount arity+152)*
        (s.axes+1)^2 := by
  have hframe := frame_cost (CompactComplexChildHeadersData.parent rho visit hactive pair) hactive
  have hexp := exponent_bound visit hactive
  have hheaders := CompactComplexChildHeadersUniform.internal_cost rho hactive pair slot rows visit
  have hs : s.axes+1≤(s.axes+1)^2 := by nlinarith
  have h1 : 1≤(s.axes+1)^2 := by nlinarith
  have hW := Nat.mul_le_mul_left (CompactComplexCallReturn.addressWidth siteCount arity) h1
  unfold entryCost
  nlinarith

theorem return_bound (rho : Fin s.chunk) (visit : Visit s.active left (k+2))
    (hactive : s.active≤s.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (slot : Fin arity) :
    returnCost rho visit hactive pair slot ≤53*(s.axes+1) := by
  have hframe := frame_cost (CompactComplexChildHeadersData.parent rho visit hactive pair) hactive
  have h0 := descriptor_lengths (CompactComplexChildHeadersData.child rho visit hactive pair slot) hactive 0
  have h1 := descriptor_lengths (CompactComplexChildHeadersData.child rho visit hactive pair slot) hactive 1
  have h2 := descriptor_lengths (CompactComplexChildHeadersData.child rho visit hactive pair slot) hactive 2
  have hexp := exponent_bound visit hactive
  unfold returnCost
  omega

private theorem square_le_power (n : ℕ) : (n+1)^2≤4*2^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    by_cases h0 : n=0
    · subst n; norm_num
    by_cases h1 : n=1
    · subst n; norm_num
    have hn : 2≤n := by omega
    rw [show 2^(n+1)=2^n*2 from pow_succ 2 n]
    nlinarith

/-- Exponential native address volume pays all polynomial geometry overhead,
without assuming an independent child-control cost envelope. -/
theorem dimension_square_le_volume (rows ell p : ℕ) (hr : 0<rows) (hG : 1≤s.guard) :
    (s.axes+1)^2≤4*CompactNativeRoleTransferBudget.volume rows s ell p := by
  have hH : s.axes≤s.H := Nat.le_mul_of_pos_right _ hG
  have ha : s.axes≤s.bits := by unfold Shape.bits; omega
  have hs := square_le_power s.bits
  have hV : 2^s.bits≤CompactNativeRoleTransferBudget.volume rows s ell p := by
    have hR : 0<2^ell := pow_pos (by decide) _
    have hw : 0<2*(CompactNativeRoleHeaders.recordWidth s p+1) := by omega
    have h0 := Nat.le_mul_of_pos_right (2^s.bits) hR
    have h1 := Nat.le_mul_of_pos_right (2^s.bits*2^ell) hw
    have h2 := Nat.le_mul_of_pos_left (CompactNativeRoleOriginal.symbols s ell p) hr
    unfold CompactNativeRoleTransferBudget.volume CompactNativeRoleOriginal.symbols
      CompactNativeRoleOriginal.inner at *
    omega
  have hsq := Nat.pow_le_pow_left (Nat.add_le_add_right ha 1) 2
  exact hsq.trans (hs.trans (Nat.mul_le_mul_left 4 hV))

/-- Entry, real return-PC decoding and parent restoration are linear in the
original native selected-role volume. Both connecting joins are also paid;
execution of the recursive child is not part of this overhead bound. -/
theorem lifecycle_linear (siteCount : ℕ) (rho : Fin s.chunk) (visit : Visit s.active left (k+2))
    (hactive : s.active≤s.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (slot : Fin arity) (rows ell p : ℕ) (hr : 0<rows) (hG : 1≤s.guard) :
    entryCost siteCount rho visit hactive pair slot rows+
      CompactComplexCallReturn.addressWidth siteCount arity+5+returnCost rho visit hactive pair slot+2 ≤
      (4*(CompactComplexChildHeadersUniform.constant+2*CompactComplexCallReturn.addressWidth siteCount arity+212))*
        CompactNativeRoleTransferBudget.volume rows s ell p := by
  have he := entry_bound siteCount rho visit hactive pair slot rows
  have hret := return_bound rho visit hactive pair slot
  have hs : s.axes+1≤(s.axes+1)^2 := by nlinarith
  have hv := dimension_square_le_volume (s:=s) rows ell p hr hG
  have h1 : 1≤(s.axes+1)^2 := by nlinarith
  have hW := Nat.mul_le_mul_left (CompactComplexCallReturn.addressWidth siteCount arity) h1
  have hmul := Nat.mul_le_mul_left
    (CompactComplexChildHeadersUniform.constant+2*CompactComplexCallReturn.addressWidth siteCount arity+212) hv
  nlinarith

end
end IntegerMultBounds.Machine.CompactComplexControllerChildBudget
