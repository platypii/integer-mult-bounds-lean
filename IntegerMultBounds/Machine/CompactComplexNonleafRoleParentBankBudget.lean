import IntegerMultBounds.Machine.CompactComplexNonleafRoleParentBank
import IntegerMultBounds.Machine.CompactComplexControllerChildBudget
import IntegerMultBounds.Machine.CompactComplexControllerExactReturnBudget

/-! The actual raw child-to-parent geometric return has a uniform native-volume
cost. Actual dependency Paths supply the parent visit and genuine child call;
retained geometry pays descriptor lengths, exponent traffic and every join.
No separate live-denominator or aggregate time allowance is needed here. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafRoleParentBankBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactComplexChildHeadersData (parent child)
open CompactComplexControllerChildPrefix (data)
open CompactComplexNonleafRoleParentBank (stackSlot)
open CompactComplexNonleafRoleChildBank (tapes control)
open CompactComplexNativeCodec (raw)
open CompactNativeRoleTransferBudget (volume)
open RecursiveChildQuotientsConstant (bits)
variable {sh : Shape} {left k levels frames returned s c : ℕ}

/-- Literal raw_runs cost: erase three changed child words, pop the saved
parent words, increment the real exponent and pay both physical joins. -/
def cost (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (ha : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity)) (slot : Fin arity) :=
  2*((data (child rho visit ha pair slot) 0).length+
    (data (child rho visit ha pair slot) 1).length+
    (data (child rho visit ha pair slot) 2).length)+14+
    CompactChildHeadersStack.cost (data (parent rho visit ha pair))+1+2*((k+2)+1)+1

def timeConstant : ℕ := 212

/-- The retained ell/p and child rows never appear in the erased geometry
words; the actual raw cost equals the already certified controller expression. -/
theorem cost_eq_return (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (ha : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity)) (slot : Fin arity) :
    cost rho visit ha pair slot=CompactComplexControllerChildBudget.returnCost rho visit ha pair slot := by
  unfold cost CompactComplexControllerChildBudget.returnCost
  omega

theorem cost_linear (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (ha : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity)) (slot : Fin arity)
    (rows ell metadataP : ℕ) (hr : 0<rows) (hG : 1≤sh.guard) :
    cost rho visit ha pair slot≤timeConstant*volume rows sh ell metadataP := by
  rw [cost_eq_return]
  have hcost := CompactComplexControllerChildBudget.return_bound rho visit ha pair slot
  have hdim := CompactComplexControllerChildBudget.dimension_square_le_volume
    (s:=sh) rows ell metadataP hr hG
  have hsq : sh.axes+1≤(sh.axes+1)^2 := by nlinarith
  unfold timeConstant
  nlinarith

/-- The visit is derived from the genuine parent dependency Path; the child
geometry is its actual call's residual coordinate, not an arbitrary address. -/
theorem cost_from_path (path : CompactRecursiveDependencyBudget.Path sh.active left (k+2) levels frames returned)
    (rho : Fin sh.chunk) (ha : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (call : Networks.ComplexRecursiveCallSchema.Call)
    (rows ell metadataP : ℕ) (hr : 0<rows) (hG : 1≤sh.guard) :
    cost rho path.visit ha pair call.slot≤timeConstant*volume rows sh ell metadataP :=
  cost_linear rho path.visit ha pair call.slot rows ell metadataP hr hG

/-- The actual descendant Path has precisely the visit used by the physical
raw child bank; it preserves the parent/child dependency boundary literally. -/
theorem child_visit (path : CompactRecursiveDependencyBudget.Path sh.active left (k+2) levels frames returned)
    (call : Networks.ComplexRecursiveCallSchema.Call) :
    (CompactRecursiveDependencyBudget.Path.child (k:=k+1) path call).visit=
      Visit.child path.visit call.slot := Subsingleton.elim _ _

/-- Bound attached to the exact physical raw child bank. The original parent
row volume pays the return, while its child rows/c remain unchanged. -/
theorem raw_linear (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (ha : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity)) (slot : Fin arity)
    (rows ell metadataP : ℕ) (hr : 0<rows) (hG : 1≤sh.guard) (payload : Tapes (1+c) 2)
    (v : Tapes (tapes s c) 2) (stack : Fin s) (f : ℤ → Fin 6) (p : ℤ)
    (hi : Placement.active (CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c)) v=
      CompactNativeRoleOriginal.bank (raw (child rho visit ha pair slot) (rows/c) ell metadataP) payload)
    (ht : v.tape (stackSlot stack)=CompactChildHeadersStack.frames f p (data (parent rho visit ha pair)))
    (hp : v.head (stackSlot stack)=CompactChildHeadersStack.top p (data (parent rho visit ha pair)))
    (hb : ∀ z,p≤z → f z=blank)
    (hx : v.tape (control 1)=BinaryDescriptorStack.descriptor (bits (k+1))) (hhx : v.head (control 1)=1) :
    HoareTime (CompactComplexNonleafRoleParentBank.program (c:=c) stack) (fun w => w=v)
      (fun w => w=CompactComplexNonleafRoleParentBank.output v stack f p (data (parent rho visit ha pair)) (k+2))
      (timeConstant*volume rows sh ell metadataP) := by
  have h := CompactComplexNonleafRoleParentBank.raw_runs rho visit ha pair slot (rows/c) ell metadataP
    payload v stack f p (k+2) (by omega) hi ht hp hb
    (by simpa only [show k+2-1=k+1 by omega] using hx) hhx
  exact h.consequence (fun _ h => h) (fun _ h => h)
    (cost_linear rho visit ha pair slot rows ell metadataP hr hG)

/-- The exact tape contract uses the true parent's dependency Path directly;
its next actual call derives the child Visit via child_visit above. -/
theorem raw_from_path
    (path : CompactRecursiveDependencyBudget.Path sh.active left (k+2) levels frames returned)
    (rho : Fin sh.chunk) (ha : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (call : Networks.ComplexRecursiveCallSchema.Call)
    (rows ell metadataP : ℕ) (hr : 0<rows) (hG : 1≤sh.guard) (payload : Tapes (1+c) 2)
    (v : Tapes (tapes s c) 2) (stack : Fin s) (f : ℤ → Fin 6) (p : ℤ)
    (hi : Placement.active (CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c)) v=
      CompactNativeRoleOriginal.bank (raw (child rho path.visit ha pair call.slot) (rows/c) ell metadataP) payload)
    (ht : v.tape (stackSlot stack)=CompactChildHeadersStack.frames f p (data (parent rho path.visit ha pair)))
    (hp : v.head (stackSlot stack)=CompactChildHeadersStack.top p (data (parent rho path.visit ha pair)))
    (hb : ∀ z,p≤z → f z=blank)
    (hx : v.tape (control 1)=BinaryDescriptorStack.descriptor (bits (k+1))) (hhx : v.head (control 1)=1) :
    HoareTime (CompactComplexNonleafRoleParentBank.program (c:=c) stack) (fun w => w=v)
      (fun w => w=CompactComplexNonleafRoleParentBank.output v stack f p (data (parent rho path.visit ha pair)) (k+2))
      (timeConstant*volume rows sh ell metadataP) :=
  raw_linear rho path.visit ha pair call.slot rows ell metadataP hr hG payload v stack f p hi ht hp hb hx hhx

/-- Actual padded descendant volume is at most twice the unpadded original
stream, so the full return overhead has one uniform fallback-volume constant. -/
theorem cost_original (c m d D G K0 ell q level : ℕ)
    (path : CompactRecursiveDependencyBudget.Path (CompactReservationNativeRows.shape c m d D G K0).active
      left (k+2) levels frames returned)
    (rho : Fin (CompactReservationNativeRows.shape c m d D G K0).chunk)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (call : Networks.ComplexRecursiveCallSchema.Call)
    (hc : 0<c) (hK : 0<K0) (hlevel : level≤CompactGlobalRowPadding.depth m d)
    (hG : 1≤G) (hDd : D≤d) (hD : CompactGlobalReservation.reservedAxes c m d G K0≤D) :
    cost rho path.visit (CompactGlobalReservation.active_le_global c m d D G K0 1 hDd) pair call.slot≤
      (2*timeConstant)*CompactFallbackAxisRun.volume D K0 ell q := by
  have hr := CompactGlobalRowPadding.rowsAt_positive c m d K0 level hc hK hlevel
  have hv := CompactComplexControllerExactReturnBudget.original_volume c m d D G K0 ell q level hc hK hD
  have h := cost_from_path path rho (CompactGlobalReservation.active_le_global c m d D G K0 1 hDd)
    pair call (CompactGlobalRowPadding.rowsAt c m d K0 level) ell
    (CompactNativeRoleReservedBridge.precision c m d D K0 q) hr hG
  have hb := h.trans (Nat.mul_le_mul_left timeConstant hv)
  simpa only [Nat.mul_left_comm,Nat.mul_assoc] using hb

/-- The true original padded geometry pays the actual raw geometric return,
with exact retained child rows, unchanged ell/p and literal popped-stack output. -/
theorem raw_original (c m d D G K0 ell q level : ℕ)
    (path : CompactRecursiveDependencyBudget.Path (CompactReservationNativeRows.shape c m d D G K0).active
      left (k+2) levels frames returned)
    (rho : Fin (CompactReservationNativeRows.shape c m d D G K0).chunk)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (call : Networks.ComplexRecursiveCallSchema.Call)
    (hc : 0<c) (hK : 0<K0) (hlevel : level≤CompactGlobalRowPadding.depth m d)
    (hG : 1≤G) (hDd : D≤d) (hD : CompactGlobalReservation.reservedAxes c m d G K0≤D)
    (payload : Tapes (1+c) 2) (v : Tapes (tapes s c) 2) (stack : Fin s) (f : ℤ → Fin 6) (p : ℤ)
    (hi : Placement.active (CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c)) v=
      CompactNativeRoleOriginal.bank
        (raw (child rho path.visit (CompactGlobalReservation.active_le_global c m d D G K0 1 hDd) pair call.slot)
          (CompactGlobalRowPadding.rowsAt c m d K0 level/c) ell
          (CompactNativeRoleReservedBridge.precision c m d D K0 q)) payload)
    (ht : v.tape (stackSlot stack)=CompactChildHeadersStack.frames f p
      (data (parent rho path.visit (CompactGlobalReservation.active_le_global c m d D G K0 1 hDd) pair)))
    (hp : v.head (stackSlot stack)=CompactChildHeadersStack.top p
      (data (parent rho path.visit (CompactGlobalReservation.active_le_global c m d D G K0 1 hDd) pair)))
    (hb : ∀ z,p≤z → f z=blank)
    (hx : v.tape (control 1)=BinaryDescriptorStack.descriptor (bits (k+1))) (hhx : v.head (control 1)=1) :
    HoareTime (CompactComplexNonleafRoleParentBank.program (c:=c) stack) (fun w => w=v)
      (fun w => w=CompactComplexNonleafRoleParentBank.output v stack f p
        (data (parent rho path.visit (CompactGlobalReservation.active_le_global c m d D G K0 1 hDd) pair)) (k+2))
      ((2*timeConstant)*CompactFallbackAxisRun.volume D K0 ell q) := by
  have hr := CompactGlobalRowPadding.rowsAt_positive c m d K0 level hc hK hlevel
  have hv := CompactComplexControllerExactReturnBudget.original_volume c m d D G K0 ell q level hc hK hD
  have h := raw_from_path path rho (CompactGlobalReservation.active_le_global c m d D G K0 1 hDd)
    pair call (CompactGlobalRowPadding.rowsAt c m d K0 level) ell
    (CompactNativeRoleReservedBridge.precision c m d D K0 q) hr hG payload v stack f p hi ht hp hb hx hhx
  exact h.consequence (fun _ h => h) (fun _ h => h)
    (by simpa only [Nat.mul_left_comm,Nat.mul_assoc] using Nat.mul_le_mul_left timeConstant hv)

end
end IntegerMultBounds.Machine.CompactComplexNonleafRoleParentBankBudget
