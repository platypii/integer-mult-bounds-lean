import IntegerMultBounds.Machine.CompactComplexNonleafRoleParentBank
import IntegerMultBounds.Machine.CompactComplexNonleafRoleParentRows

/-! A physical decoded-parent continuation restores the actual saved geometry
and exponent, then multiplies only the parent's row descriptor. Payloads remain
literal and arbitrary. Live-grid promotion and full recursive correctness are
later obligations, not assumptions of this physical composition. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafRoleParentContinuation
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactComplexChildHeadersData (parent child)
open CompactComplexNativeCodec (raw)
open CompactComplexNonleafRoleChildBank (tapes control)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ} {sh : Shape} {left k : ℕ}

abbrev placement := CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c)

def rowProgram (s c : ℕ) := Placement.placed
  (extend (ButterflyAxisHeadersArithmetic.compile (a:=2)
    (CompactComplexNonleafRoleParentRows.schedule c)).2 (CompactNativeRoleInstall.rawCount c))
  (placement (s:=s) (c:=c))

def rowOutput (v : Tapes (tapes s c) 2) (stage : ActivePrefixStageParameters.Stage sh)
    (rows ell precision : ℕ) (payload : Tapes (1+c) 2) :=
  Placement.replace placement v
    (CompactNativeRoleOriginal.bank (raw stage rows ell precision) payload)

theorem rows_runs (v : Tapes (tapes s c) 2) (stage : ActivePrefixStageParameters.Stage sh)
    (rows ell precision : ℕ) (payload : Tapes (1+c) 2) (hr : 0<rows/c) (hd : c ∣ rows)
    (hi : Placement.active placement v=
      CompactNativeRoleOriginal.bank (raw stage (rows/c) ell precision) payload) :
    HoareTime (rowProgram s c) (fun z => z=v)
      (fun z => z=rowOutput v stage rows ell precision payload)
      (1000*(c+1)*rows) := by
  have h := ButterflyAxisHeadersArithmetic.schedule_runs (a:=2)
    (CompactComplexNonleafRoleParentRows.schedule c) (raw stage (rows/c) ell precision)
    (CompactComplexNonleafRoleParentRows.schedule_valid c sh (rows/c) ell precision stage.rho
      stage.left stage.f stage.slots stage.right stage.source.val stage.target.val hr)
  unfold raw CompactNativeRoleConjugatedLifecycle.rawState at h
  rw [CompactComplexNonleafRoleParentRows.schedule_eval,Nat.div_mul_cancel hd] at h
  have h' := Placement.hoare_at (hoare_extend_eq h (CompactNativeRoleInstall.blankRaw payload))
    placement v hi
  exact h'.consequence (fun _ h => h) (by rintro z ⟨w,rfl,rfl⟩; rfl)
    (CompactComplexNonleafRoleTransferBudget.restore_linear c sh rows ell precision stage.rho
      stage.left stage.f stage.slots stage.right stage.source.val stage.target.val
      (by have := Nat.div_le_self rows c; omega) hd)

def program (stack : Fin s) := seq (CompactComplexNonleafRoleParentBank.program (c:=c) stack)
  (rowProgram s c)

def geometryCost (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (e : ℕ) :=
  let data := CompactComplexControllerChildPrefix.data (child rho visit hactive pair coordinate)
  2*((data 0).length+(data 1).length+(data 2).length)+14+
    CompactChildHeadersStack.cost (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair))+1+
    2*(e+1)+1

def output (v : Tapes (tapes s c) 2) (stack : Fin s) (f : ℤ → Fin 6) (p : ℤ) (e : ℕ)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (rows ell precision : ℕ)
    (payload : Tapes (1+c) 2) :=
  rowOutput (CompactComplexNonleafRoleParentBank.output v stack f p
    (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)) e)
    (parent rho visit hactive pair) rows ell precision payload

/-- The same fixed continuation is valid for every genuine saved parent
frame and arbitrary actual child result payload. Both joins and row arithmetic
are charged; no completed-child execution certificate is supplied. -/
theorem runs (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (rows ell precision : ℕ) (payload : Tapes (1+c) 2)
    (v : Tapes (tapes s c) 2) (stack : Fin s) (f : ℤ → Fin 6) (p : ℤ) (e : ℕ) (he : 0<e)
    (hr : 0<rows/c) (hd : c ∣ rows)
    (hi : Placement.active placement v=
      CompactNativeRoleOriginal.bank (raw (child rho visit hactive pair coordinate) (rows/c) ell precision) payload)
    (ht : v.tape (CompactComplexNonleafRoleParentBank.stackSlot stack)=CompactChildHeadersStack.frames f p
      (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)))
    (hp : v.head (CompactComplexNonleafRoleParentBank.stackSlot stack)=CompactChildHeadersStack.top p
      (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)))
    (hb : ∀ z,p≤z → f z=blank)
    (hx : v.tape (control 1)=BinaryDescriptorStack.descriptor (bits (e-1))) (hhx : v.head (control 1)=1) :
    HoareTime (program (c:=c) stack) (fun z => z=v)
      (fun z => z=output v stack f p e rho visit hactive pair rows ell precision payload)
      (geometryCost rho visit hactive pair coordinate e+1+1000*(c+1)*rows) := by
  have h0 := CompactComplexNonleafRoleParentBank.raw_runs rho visit hactive pair coordinate
    (rows/c) ell precision payload v stack f p e he hi ht hp hb hx hhx
  have h1 := rows_runs (CompactComplexNonleafRoleParentBank.output v stack f p
    (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)) e)
    (parent rho visit hactive pair) rows ell precision payload hr hd
    (CompactComplexNonleafRoleParentBank.output_active rho visit hactive pair coordinate
      (rows/c) ell precision payload v stack f p e hi)
  exact h0.seq h1

theorem output_active (v : Tapes (tapes s c) 2) (stack : Fin s) (f : ℤ → Fin 6) (p : ℤ) (e : ℕ)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (rows ell precision : ℕ)
    (payload : Tapes (1+c) 2) :
    Placement.active placement (output v stack f p e rho visit hactive pair rows ell precision payload)=
      CompactNativeRoleOriginal.bank (raw (parent rho visit hactive pair) rows ell precision) payload :=
  Placement.active_replace _ _ _

/-- Header arithmetic leaves the geometric/PC/live stack frame from the
preceding restoration entirely unchanged. -/
theorem output_extra (v : Tapes (tapes s c) 2) (stack : Fin s) (f : ℤ → Fin 6) (p : ℤ) (e : ℕ)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (rows ell precision : ℕ)
    (payload : Tapes (1+c) 2) :
    Placement.extra placement (output v stack f p e rho visit hactive pair rows ell precision payload)=
      Placement.extra placement (CompactComplexNonleafRoleParentBank.output v stack f p
        (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)) e) := by
  simp only [output,rowOutput,Placement.replace,Placement.extra_combine]

end
end IntegerMultBounds.Machine.CompactComplexNonleafRoleParentContinuation
