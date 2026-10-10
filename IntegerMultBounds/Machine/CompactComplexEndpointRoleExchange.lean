import IntegerMultBounds.Machine.NamedRoleWordExchange
import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafScalarInitialReadiness
import IntegerMultBounds.Networks.ComplexFramedExecution

/-! The actual complex25 named X/Y banks are physically exchanged once each.
The fixed original address enumeration stays opaque; scratch and every tape
head are preserved. Uniform cost is charged against parent native volume. -/
namespace IntegerMultBounds.Machine.CompactComplexEndpointRoleExchange
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexRolePhaseSite (roleCount roleEncoding)
abbrev Address := Networks.Wires.Address 25
abbrev Wire := Networks.Wires.ComplexRole 25
local instance : DecidableEq (Networks.Wires.Invocation 25 ×
    (Networks.NeighborCounts.ComplexPairs 25 ⊕ Fin (25+1))) := Classical.decEq _
variable {s u : ℕ}

abbrev tapes (s u : ℕ) := CompactComplexNativeCodecFrame.permanentTapes s roleCount+u

def port (a : Wire) : Fin (tapes s u) :=
  Fin.castAdd u (CompactComplexSpectatorTargetBank.roleSlot (roleEncoding a))

theorem port_injective : Function.Injective (port (s:=s) (u:=u)) := by
  intro a b h
  have hv := congrArg (fun i : Fin (tapes s u) => i.val) h
  have h0 : CompactComplexSpectatorTargetBank.roleSlot (s:=s) (roleEncoding a)=
      CompactComplexSpectatorTargetBank.roleSlot (roleEncoding b) :=
    Fin.ext hv
  exact roleEncoding.injective (CompactComplexSpectatorTargetBank.role_injective h0)

private theorem enumeration_exists : ∃ as : List Address,as.Nodup ∧ ∀ a,a∈as := by
  classical
  exact ⟨Finset.univ.toList,Finset.nodup_toList _,fun a => Finset.mem_toList.mpr (Finset.mem_univ a)⟩

/-- A fixed complete finite list, without kernel reduction of the layout. -/
def addresses : List Address := Classical.choose enumeration_exists

theorem addresses_nodup : addresses.Nodup := (Classical.choose_spec enumeration_exists).1
theorem addresses_complete (a : Address) : a∈addresses := (Classical.choose_spec enumeration_exists).2 a

/-- Every actual named role occupies its original permanent caller port. -/
def bank (v : Tapes (tapes s u) 2) {sh : Shape} {rows ell : ℕ}
    (data : Wire → Array sh rows ell) := NamedRoleWordExchange.bank port v data

def program : Σ q,Program (tapes s u) q 2 :=
  NamedRoleWordExchange.compile port port_injective (by
    unfold tapes CompactComplexNativeCodecFrame.permanentTapes
      CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes
    omega) addresses

theorem execute_route {X : Type*} (data : Wire → X) :
    NamedRoleWordExchange.execute addresses data=
      fun a => data (Networks.ComplexFramedExecution.route a) := by
  obtain ⟨hx,hy,hs⟩ := NamedRoleWordExchange.execute_formula addresses addresses_nodup data
  funext a
  rcases a with a | a | a
  · simpa only [addresses_complete a,ite_true,Networks.ComplexFramedExecution.route] using hx a
  · simpa only [addresses_complete a,ite_true,Networks.ComplexFramedExecution.route] using hy a
  · exact hs a

def constant := 10*addresses.length

/-- Full physical exchange of all actual X/Y arrays, including head restoration
and preservation of the original scratch-role words. -/
theorem runs (v : Tapes (tapes s u) 2) (sh : Shape) (parentRows ell p : ℕ)
    (hr : 0<parentRows/roleCount)
    (data : Wire → Array sh (parentRows/roleCount) ell)
    (hw : ∀ a i,(data a i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (data a i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (hh : ∀ a,v.head (port a)=0) :
    HoareTime (program (s:=s) (u:=u)).2 (fun z => z=bank v data)
      (fun z => z=bank v (fun a => data (Networks.ComplexFramedExecution.route a)))
      (constant*CompactNativeRoleTransferBudget.volume parentRows sh ell p) := by
  have h := NamedRoleWordExchange.compile_runs port port_injective (by
    unfold tapes CompactComplexNativeCodecFrame.permanentTapes
      CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes
    omega) addresses v sh (parentRows/roleCount) ell p hr data hw hh
  rw [execute_route] at h
  apply h.consequence (fun _ h => h) (fun _ h => h)
  have hv : 0<CompactNativeRoleTransferBudget.volume (parentRows/roleCount) sh ell p :=
    Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
  have hle : CompactNativeRoleTransferBudget.volume (parentRows/roleCount) sh ell p≤
      CompactNativeRoleTransferBudget.volume parentRows sh ell p :=
    Nat.mul_le_mul_right _ (Nat.div_le_self _ _)
  unfold constant
  nlinarith

/-- Every physical head, including non-role controller and scratch heads, is
literally restored by the routed endpoint. -/
theorem endpoint_heads (v : Tapes (tapes s u) 2) {sh : Shape} {rows ell : ℕ}
    (data : Wire → Array sh rows ell) :
    (bank v (fun a => data (Networks.ComplexFramedExecution.route a))).head=(bank v data).head := rfl

/-- Original named scratch roles are retained byte for byte. -/
theorem endpoint_scratch (v : Tapes (tapes s u) 2) {sh : Shape} {rows ell : ℕ}
    (data : Wire → Array sh rows ell)
    (a : Networks.Wires.Invocation 25 × (Networks.NeighborCounts.ComplexPairs 25 ⊕ Fin 26)) :
    (bank v (fun a => data (Networks.ComplexFramedExecution.route a))).tape (port (Sum.inr (Sum.inr a)))=
      (bank v data).tape (port (Sum.inr (Sum.inr a))) := by
  simp only [bank,NamedRoleWordExchange.bank_role port port_injective,
    Networks.ComplexFramedExecution.route]

/-- Execute directly from an existing caller carrying the original named words;
no initialized replacement bank or local execution oracle is supplied. -/
theorem runs_from_words (v : Tapes (tapes s u) 2) (sh : Shape) (parentRows ell p : ℕ)
    (hr : 0<parentRows/roleCount)
    (data : Wire → Array sh (parentRows/roleCount) ell)
    (hw : ∀ a i,(data a i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (data a i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (hh : ∀ a,v.head (port a)=0)
    (hs : ∀ a,v.tape (port a)=NativeZeroPadding.word (NativeZeroPaddingArray.word (data a))) :
    HoareTime (program (s:=s) (u:=u)).2 (fun z => z=v)
      (fun z => z=bank v (fun a => data (Networks.ComplexFramedExecution.route a)))
      (constant*CompactNativeRoleTransferBudget.volume parentRows sh ell p) := by
  have h := runs v sh parentRows ell p hr data hw hh
  have he : bank v data=v := NamedRoleWordExchange.bank_eq port v data hs
  rwa [he] at h

/-- Controller, numeric, source and external scratch words outside the original
named role ports all remain byte for byte. -/
theorem endpoint_frame (v : Tapes (tapes s u) 2) {sh : Shape} {rows ell : ℕ}
    (data : Wire → Array sh rows ell) (i : Fin (tapes s u))
    (hi : ∀ a,port a≠i) :
    (bank v (fun a => data (Networks.ComplexFramedExecution.route a))).tape i=(bank v data).tape i := by
  exact (NamedRoleWordExchange.bank_frame port v _ i hi).trans
    (NamedRoleWordExchange.bank_frame port v data i hi).symm

/-- An arbitrary workspace suffix is untouched by every original bank swap. -/
theorem endpoint_suffix (v : Tapes (tapes s u) 2) {sh : Shape} {rows ell : ℕ}
    (data : Wire → Array sh rows ell) (i : Fin u) :
    (bank v (fun a => data (Networks.ComplexFramedExecution.route a))).tape
      (Fin.natAdd (CompactComplexNativeCodecFrame.permanentTapes s roleCount) i)=
    v.tape (Fin.natAdd (CompactComplexNativeCodecFrame.permanentTapes s roleCount) i) := by
  apply NamedRoleWordExchange.bank_frame
  intro a h
  have hv := congrArg (fun j : Fin (tapes s u) => j.val) h
  have ha := (CompactComplexSpectatorTargetBank.roleSlot (s:=s) (roleEncoding a)).isLt
  simp only [port,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

/-- Original fixed role encoding of a complete array family, retaining the
independent master word and its head. -/
def payload {sh : Shape} {rows ell : ℕ} (source : ℤ → Fin 6) (sourceHead : ℤ)
    (data : Wire → Array sh rows ell) : Tapes (1+roleCount) 2 :=
  CyclicRowCopy.payload source
    (fun j => NativeZeroPadding.word (NativeZeroPaddingArray.word (data (roleEncoding.symm j))))
    sourceHead (fun _ => 0)

/-- Physical named words are derived from the literal original caller bank,
with any controller, master, storage and workspace frame. -/
theorem caller_roles {sh : Shape} {rows ell : ℕ}
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes s 2) (extra : Tapes u 2) (source : ℤ → Fin 6) (sourceHead : ℤ)
    (data : Wire → Array sh rows ell) (a : Wire) :
    let v := (CompactComplexNativeCodecFrame.bank control queue scalar stage tail storage
      (payload source sourceHead data)).append extra
    v.head (port a)=0 ∧
    v.tape (port a)=NativeZeroPadding.word (NativeZeroPaddingArray.word (data a)) := by
  dsimp only
  have h := CompactComplexSpectatorTargetBank.role_bank control queue scalar stage tail storage
    (payload source sourceHead data) (roleEncoding a)
  simpa only [port,Tapes.append,Fin.addCases_left,payload,CyclicRowCopy.payload,
    Fin.addCases_right,Equiv.symm_apply_apply] using h

/-- Actual original caller specialization: all swap prerequisites are derived
from its physical array payload, and the complete routed endpoint is literal. -/
theorem runs_caller (sh : Shape) (parentRows ell p : ℕ) (hr : 0<parentRows/roleCount)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes s 2) (extra : Tapes u 2) (source : ℤ → Fin 6) (sourceHead : ℤ)
    (data : Wire → Array sh (parentRows/roleCount) ell)
    (hw : ∀ a i,(data a i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (data a i).2.length=CompactNativeRoleHeaders.recordWidth sh p) :
    let v := (CompactComplexNativeCodecFrame.bank control queue scalar stage tail storage
      (payload source sourceHead data)).append extra
    HoareTime (program (s:=s) (u:=u)).2 (fun z => z=v)
      (fun z => z=bank v (fun a => data (Networks.ComplexFramedExecution.route a)))
      (constant*CompactNativeRoleTransferBudget.volume parentRows sh ell p) := by
  dsimp only
  apply runs_from_words _ sh parentRows ell p hr data hw
  · intro a
    exact (caller_roles control queue scalar stage tail storage extra source sourceHead data a).1
  · intro a
    exact (caller_roles control queue scalar stage tail storage extra source sourceHead data a).2

end
end IntegerMultBounds.Machine.CompactComplexEndpointRoleExchange
