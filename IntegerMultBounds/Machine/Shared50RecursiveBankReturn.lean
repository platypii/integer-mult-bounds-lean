import IntegerMultBounds.Machine.Shared50RecursiveBank
import IntegerMultBounds.Machine.RecursiveDigitRoleBank

/-! Actual width-one base and shared ancestor-header return on the permanent
recursive bank. The PC is left encoded for the controller's separate pop block. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveBankReturn
noncomputable section
open Networks
open Shared50ModularControl (prime)
open SharedBankStageInput (raw)
open Shared50RecursiveBank
open RecursiveInterchangeLayout (Descriptor volume child)
variable {t u m k : ℕ}

def base (wire : Fin t) := SharedBankFamily.ofProgram
  (RecursiveDigitRoleBank.program (u := AuxCount u) wire)

def restore := SharedBankFamily.ofProgram
  (RecursiveChildReturnRoleBank.restoreProgram (t := t) (u := 3+(1+(1+u))))

theorem base_hoare (v : Descriptor) (hw : v.width = 1) (wire : Fin t) (roles : Tapes t prime)
    (hs : Fin 6 → List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (node scalar : Tapes 1 prime) (aux : Tapes u prime) (st : Tapes 2 prime)
    (x : Fin (volume prime v) → Fin 4) (hh : roles.head wire = 0)
    (ht : roles.tape wire = RecursiveShiftRoleBank.source x)
    (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive) :
    HoareTime (base (u := u) wire).program
      (fun w => w = raw (bank roles hs f p node scalar aux st) (base (u := u) wire).tapes)
      (fun w => w = raw (bank (RecursiveShiftRoleBank.updated roles wire (RecursiveDigitRoleBank.array hw x))
        hs f p node scalar aux st) (base (u := u) wire).tapes)
      (RecursiveDigitRoleBank.coefficient*volume prime v) := by
  have h := RecursiveDigitRoleBank.realizes hw wire roles hs (auxiliary f p node scalar aux st) x hh ht hv hp
  simp only [SharedBankRawCompose.bank_eq_raw] at h
  exact h

/-- Exact physical restoration cost, independently of how the active headers
were constructed. All three other stacks and both counters are spectators. -/
theorem restore_hoare (roles : Tapes t prime) (old hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (aux : Tapes u prime) (st : Tapes 2 prime) (code : FiniteReturnStack.Code k)
    (hd : RecursiveStackAllocation.Available 0 st) :
    HoareTime (restore (t := t) (u := u)).program
      (fun w => w = raw (bank roles hs f p node scalar aux (RecursiveChildCallSetup.savedStacks old st code))
        (restore (t := t) (u := u)).tapes)
      (fun w => w = raw (bank roles old f p node scalar aux (RecursiveChildCallReturn.pending st code))
        (restore (t := t) (u := u)).tapes)
      (RecursiveChildCallReturn.cost old hs) := by
  have h := RecursiveChildReturnRoleBank.restores roles old hs
    ((RecursiveCallBank.work f p).append (node.append (scalar.append aux))) st code hd
  simp only [RecursiveChildReturnRoleBank.bank,SharedBankRawCompose.bank_eq_raw] at h
  exact h

/-- Bound restoration by the original role-parent volume, with same-row child
headers. No original-parent row split is repeated at a recursive call. -/
theorem restore_linear (b : ℕ) (v : Descriptor) (i j : Fin m) (hw : v.width=m*b)
    (hp : v.Positive) (old hs : Fin 6 → List Bool)
    (ho : RecursiveDimensionBank.Headers v old)
    (hc : RecursiveDimensionBank.Headers (child prime 1 b v i j) hs)
    (roles : Tapes t prime) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (node scalar : Tapes 1 prime) (aux : Tapes u prime) (st : Tapes 2 prime)
    (code : FiniteReturnStack.Code k) (hd : RecursiveStackAllocation.Available 0 st) :
    HoareTime (restore (t := t) (u := u)).program
      (fun w => w = raw (bank roles hs f p node scalar aux (RecursiveChildCallSetup.savedStacks old st code))
        (restore (t := t) (u := u)).tapes)
      (fun w => w = raw (bank roles old f p node scalar aux (RecursiveChildCallReturn.pending st code))
        (restore (t := t) (u := u)).tapes)
      (127*volume prime v) :=
  (restore_hoare roles old hs f p node scalar aux st code hd).consequence
    (fun _ h => h) (fun _ h => h)
    (RecursiveRoleChildCallSetup.restore_cost_le Shared50ModularControl.prime_prime.two_le b v i j hw hp old hs ho hc)

theorem pending_pc (roles : Tapes t prime) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (aux : Tapes u prime) (st : Tapes 2 prime) (code : FiniteReturnStack.Code k) :
    (bank roles hs f p node scalar aux (RecursiveChildCallReturn.pending st code)).head (returnSlot 1) = st.head 1+k ∧
    (bank roles hs f p node scalar aux (RecursiveChildCallReturn.pending st code)).tape (returnSlot 1) =
      FiniteReturnStack.wordPart (st.tape 1) (st.head 1) code k le_rfl := by
  simp only [bank,RecursiveCallBank.bank,RecursiveShiftRoleBank.common,returnSlot,Tapes.append,
    Fin.addCases_right,RecursiveChildCallReturn.pending,FiniteReturnStackAt.pushed,
    SharedPlacementAlphabet.setTape,Function.update_self]
  trivial


private theorem setTape_right {l r a : ℕ} (v : Tapes l a) (w : Tapes r a) (i : Fin r)
    (f : ℤ → Fin (a+4)) (p : ℤ) :
    SharedPlacementAlphabet.setTape (v.append w) (Fin.natAdd l i) f p =
      v.append (SharedPlacementAlphabet.setTape w i f p) := by
  unfold SharedPlacementAlphabet.setTape Tapes.append
  congr 1 <;> funext j <;> induction j using Fin.addCases <;> simp [Function.update_apply,Fin.ext_iff]
  all_goals rename_i z; intro h; have hz := z.isLt; omega

/-- The actual decoded-pop endpoint restores precisely the old global bank. -/
theorem reset_pending (roles : Tapes t prime) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (aux : Tapes u prime) (st : Tapes 2 prime) (code : FiniteReturnStack.Code k) :
    SharedPlacementAlphabet.setTape
      (bank roles hs f p node scalar aux (RecursiveChildCallReturn.pending st code))
      (returnSlot 1) (st.tape 1) (st.head 1) = bank roles hs f p node scalar aux st := by
  unfold bank RecursiveCallBank.bank RecursiveShiftRoleBank.common returnSlot
  rw [setTape_right,setTape_right,setTape_right]
  unfold RecursiveChildCallReturn.pending FiniteReturnStackAt.pushed
  rw [SharedPlacementAlphabet.setTape_setTape,SharedPlacementAlphabet.setTape_self]

end
end IntegerMultBounds.Machine.Shared50RecursiveBankReturn
