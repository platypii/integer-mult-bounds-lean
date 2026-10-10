import IntegerMultBounds.Machine.NativeEndpointCharacterCopy
import IntegerMultBounds.Machine.CompactComplexScalarCountLifecycle

/-! Uniform endpoint rotation reuses the character adapter's private original
raw header copy. The actual opaque role divisor computes full polynomial
coefficient count27; parent row descriptors remain retained. -/
namespace IntegerMultBounds.Machine.NativeUniformPolynomialRotationHeaders
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open ActiveRepairRankHeadersCommands (bank)
open CompactComplexScalarCountLifecycle (roleDivisor roleDivisor_eq)
open SharedPlacementAlphabet (setTape)
variable {s : Shape} {t : ℕ}
attribute [local irreducible] CompactComplexRolePhaseSite.roleCount roleDivisor

def count (v : Stage s) (parentRows ell p : ℕ) : Tapes 67 2 :=
  (bank (CompactComplexScalarCountHeaders.roleFinished roleDivisor s parentRows ell p
    v.rho v.left v.f v.slots v.right v.source.val v.target.val)).append
      (FixedHeaderBankCopy.empty 24)
def program := extend (CompactComplexScalarCountHeaders.roleProgram roleDivisor) 24
def cost (v : Stage s) (parentRows ell p : ℕ) :=
  ButterflyAxisHeadersArithmetic.scheduleCost (CompactComplexScalarCountHeaders.roleSchedule roleDivisor)
    (NativeEndpointCharacterPrepare.raw v parentRows ell p)

theorem divisor_positive : 0<roleDivisor := by
  rw [roleDivisor_eq]
  norm_num [CompactComplexRolePhaseSite.roleCount]

theorem runs (v : Stage s) (parentRows ell p : ℕ)
    (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk) :
    HoareTime program (fun z => z=NativeEndpointCharacterPrepare.input v parentRows ell p)
      (fun z => z=count v parentRows ell p) (cost v parentRows ell p) :=
  hoare_extend_eq (CompactComplexScalarCountHeaders.role_runs roleDivisor s parentRows ell p
    v.rho v.left v.f v.slots v.right v.source.val v.target.val divisor_positive hG hA hK)
    (FixedHeaderBankCopy.empty 24)

theorem cost_linear (v : Stage s) (parentRows ell p : ℕ)
    (hr : 0<parentRows) (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk) :
    cost v parentRows ell p≤CompactComplexScalarCountBudget.roleConstant roleDivisor*
      (parentRows*2^s.bits*2^ell) :=
  CompactComplexScalarCountBudget.role_setup_cost roleDivisor s parentRows ell p
    v.rho v.left v.f v.slots v.right v.source.val v.target.val hr (Nat.mul_pos hA hG) hK

def eraseCount := CompactComplexScalarCountBudget.eraseProgram (27 : Fin 67)

theorem erased_count (v : Stage s) (parentRows ell p : ℕ) :
    setTape (count v parentRows ell p) 27 (fun _ => blank) 0=
      NativeEndpointCharacterPrepare.input v parentRows ell p := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases (m:=43) (n:=24) with
    | left i =>
      induction i using Fin.addCases (m:=28) (n:=15) with
      | left i =>
        fin_cases i <;> rfl
      | right i =>
        have hi : Fin.castAdd 24 (Fin.natAdd 28 i)≠(27 : Fin 67) := by
          intro h
          have hv := congrArg Fin.val h
          change 28+i.val=27 at hv
          omega
        simp [count,bank,CleanSubbank.bank,Tapes.append,hi]
    | right i =>
      have hi : Fin.natAdd 43 i≠(27 : Fin 67) := by
        intro h
        have hv := congrArg Fin.val h
        change 43+i.val=27 at hv
        omega
      simp [count,Tapes.append,hi]

theorem erase_count_runs (v : Stage s) (parentRows ell p : ℕ) (hr : 0<parentRows/roleDivisor) :
    HoareTime eraseCount (fun z => z=count v parentRows ell p)
      (fun z => z=NativeEndpointCharacterPrepare.input v parentRows ell p)
      (8*((parentRows/roleDivisor)*2^s.bits*2^ell)) := by
  have hn : 1≤(parentRows/roleDivisor)*2^s.bits*2^ell := Nat.mul_pos (Nat.mul_pos hr (by positivity)) (by positivity)
  have h := CompactComplexScalarCountBudget.erase_runs_linear (27 : Fin 67)
    (count v parentRows ell p) ((parentRows/roleDivisor)*2^s.bits*2^ell) hn rfl rfl
  rwa [erased_count] at h

def erase := FixedHeaderSparseBankCopy.cleanup (a:=2)
  (by omega : 0<t+15) NativeEndpointCharacterCopy.destination
  NativeEndpointCharacterCopy.destination_injective (by decide : 15≤67)

theorem erase_runs (caller : Tapes t 2) (v : Stage s) (parentRows ell p : ℕ) :
    HoareTime (erase (t:=t))
      (fun z => z=caller.append (NativeEndpointCharacterPrepare.input v parentRows ell p))
      (fun z => z=caller.append (FixedHeaderBankCopy.empty 67))
      (FixedHeaderBankCopy.cleanupCost (t:=t) (NativeEndpointCharacterCopy.words v parentRows ell p)) := by
  have h := FixedHeaderSparseBankCopy.cleans (by omega : 0<t+15)
    NativeEndpointCharacterCopy.destination NativeEndpointCharacterCopy.destination_injective
    (by decide : 15≤67) caller (NativeEndpointCharacterCopy.words v parentRows ell p)
  rwa [←NativeEndpointCharacterCopy.initial_eq] at h

end
end IntegerMultBounds.Machine.NativeUniformPolynomialRotationHeaders
