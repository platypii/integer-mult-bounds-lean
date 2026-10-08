import IntegerMultBounds.Machine.Shared50RecursiveImplementation
import IntegerMultBounds.Machine.Shared50RecursiveRoot
import IntegerMultBounds.Machine.Shared50RecursiveBlockExecution
import IntegerMultBounds.Machine.Shared50RecursiveReturnExecution
import IntegerMultBounds.Machine.Shared50RecursiveBankReturn

/-! Actual base-case trace through the concrete cyclic machine: interchange,
shared header restoration, physical PC pop and the charged return edge. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveBaseExecution
noncomputable section
open Networks
open Shared50ModularControl (prime)
open Shared50NodeSegments (payloadCount io)
open Shared50RecursiveImplementation (commonCount implementation width pcStack)
open Shared50RecursiveControl
open Shared50RecursiveBank (bank)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedBankStageInput (raw)
variable {k : ℕ}
attribute [local irreducible] Shared50PieceSchedule.pieces Shared50FixedControl.control

def entryConfig (capacity : Fintype.card PC ≤ 2^k) (pc : PC) (v : Tapes commonCount prime) :=
  ((raw v (tapeCount capacity width pcStack (implementation k))).start
    (family capacity width pcStack (implementation k) (encoding pc))).mapState
      (FiniteFlow.embed (states capacity width pcStack (implementation k)) (encoding pc))

/-- No abstract base or return block is assumed. The actual concrete graph
returns the transformed stream to the physically decoded caller address. -/
theorem base_return (capacity : Fintype.card PC ≤ 2^k) (target : PC)
    (v : Descriptor) (hw : v.width=1) (hp : v.Positive)
    (roles : Tapes payloadCount prime) (old hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (aux : Tapes 0 prime) (st : Tapes 2 prime)
    (hd : RecursiveStackAllocation.Available 0 st)
    (hpc : RecursiveStackAllocation.Available 1 st)
    (x : Fin (volume prime v) → Fin 4) (hh : roles.head io=0)
    (ht : roles.tape io=RecursiveShiftRoleBank.source x) :
    ∃ steps ≤ RecursiveDigitRoleBank.coefficient*volume prime v+
        RecursiveChildCallReturn.cost old hs+k+4,
      run (Shared50RecursiveControl.program capacity width pcStack (implementation k)) steps
        (entryConfig capacity .base (bank roles hs f p node scalar aux
          (RecursiveChildCallSetup.savedStacks old st (FiniteReturnStack.address capacity (encoding target))))) =
      some (entryConfig capacity target (bank
        (RecursiveShiftRoleBank.updated roles io (RecursiveDigitRoleBank.array hw x)) old f p node scalar aux st)) := by
  let code := FiniteReturnStack.address capacity (encoding target)
  let updated := RecursiveShiftRoleBank.updated roles io (RecursiveDigitRoleBank.array hw x)
  let before := bank roles hs f p node scalar aux (RecursiveChildCallSetup.savedStacks old st code)
  let middle := bank updated hs f p node scalar aux (RecursiveChildCallSetup.savedStacks old st code)
  let pending := bank updated old f p node scalar aux (RecursiveChildCallReturn.pending st code)
  let after := bank updated old f p node scalar aux st
  have hb := Shared50RecursiveBankReturn.base_hoare v hw io roles hs f p node scalar aux
    (RecursiveChildCallSetup.savedStacks old st code) x hh ht hv hp
  have hr := Shared50RecursiveBankReturn.restore_hoare updated old hs f p node scalar aux st code hd
  obtain ⟨nb,hnb,hbase⟩ := Shared50RecursiveBlockExecution.block_jump capacity width pcStack (implementation k)
    .base .restore before middle (RecursiveDigitRoleBank.coefficient*volume prime v) hb (fun _ => rfl)
  obtain ⟨nr,hnr,hrestore⟩ := Shared50RecursiveBlockExecution.block_jump capacity width pcStack (implementation k)
    .restore .pop middle pending (RecursiveChildCallReturn.cost old hs) hr (fun _ => rfl)
  obtain ⟨hhead,htape⟩ := Shared50RecursiveBankReturn.pending_pc updated old f p node scalar aux st code
  have hfree : ∀ j < k, st.tape 1 (st.head 1+j)=blank := RecursiveStackAllocation.pc_free 1 st hpc
  have hpop := Shared50RecursiveReturnExecution.pop_jump capacity width pcStack (implementation k)
    target pending (st.tape 1) (st.head 1) htape hhead hfree
  have hreset : SharedPlacementAlphabet.setTape pending pcStack (st.tape 1) (st.head 1) = after :=
    Shared50RecursiveBankReturn.reset_pending updated old f p node scalar aux st code
  rw [hreset] at hpop
  change run (Shared50RecursiveControl.program capacity width pcStack (implementation k)) nb
    (entryConfig capacity .base before) = some (entryConfig capacity .restore middle) at hbase
  change run (Shared50RecursiveControl.program capacity width pcStack (implementation k)) nr
    (entryConfig capacity .restore middle) = some (entryConfig capacity .pop pending) at hrestore
  change run (Shared50RecursiveControl.program capacity width pcStack (implementation k)) (k+2)
    (entryConfig capacity .pop pending) = some (entryConfig capacity target after) at hpop
  refine ⟨nb+nr+(k+2),by omega,?_⟩
  rw [run_add,run_add,hbase,Option.bind_some,hrestore,Option.bind_some]
  exact hpop

/-- The actual width guard and complete base/return path start at the graph's
initial state and preserve all ancestor work and stacks. -/
theorem guard_base_return (capacity : Fintype.card PC ≤ 2^k) (target : PC)
    (v : Descriptor) (hw : v.width=1) (hp : v.Positive)
    (roles : Tapes payloadCount prime) (old hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (aux : Tapes 0 prime) (st : Tapes 2 prime)
    (hd : RecursiveStackAllocation.Available 0 st)
    (hpc : RecursiveStackAllocation.Available 1 st)
    (x : Fin (volume prime v) → Fin 4) (hh : roles.head io=0)
    (ht : roles.tape io=RecursiveShiftRoleBank.source x) :
    ∃ steps ≤ RecursiveDigitRoleBank.coefficient*volume prime v+
        RecursiveChildCallReturn.cost old hs+k+7,
      run (Shared50RecursiveControl.program capacity width pcStack (implementation k)) steps
        ((raw (bank roles hs f p node scalar aux
          (RecursiveChildCallSetup.savedStacks old st (FiniteReturnStack.address capacity (encoding target))))
          (tapeCount capacity width pcStack (implementation k))).start
          (Shared50RecursiveControl.program capacity width pcStack (implementation k))) =
      some (entryConfig capacity target (bank
        (RecursiveShiftRoleBank.updated roles io (RecursiveDigitRoleBank.array hw x)) old f p node scalar aux st)) := by
  let before := bank roles hs f p node scalar aux
    (RecursiveChildCallSetup.savedStacks old st (FiniteReturnStack.address capacity (encoding target)))
  have hvwidth : Counter.value (hs 3) = 1 := (hv.1 3).trans hw
  obtain ⟨ng,hng,hguard⟩ := Shared50RecursiveExecution.guard_jump capacity width pcStack (implementation k)
    before (hs 3) rfl (BinaryDescriptorStackRoundtrip.descriptor_encoded (hs 3)).symm (hv.2 3)
  have hbranch : Shared50RecursiveExecution.branch (Counter.value (hs 3)) = PC.base := by
    unfold Shared50RecursiveExecution.branch
    rw [hvwidth]
    rfl
  rw [hbranch] at hguard
  obtain ⟨nb,hnb,hbase⟩ := base_return capacity target v hw hp roles old hs hv f p node scalar aux st hd hpc x hh ht
  refine ⟨ng+nb,by omega,?_⟩
  rw [run_add,hguard,Option.bind_some]
  exact hbase

/-- The actual padded halt node stops the enclosing graph on the exact bank. -/
theorem halt_entry (capacity : Fintype.card PC ≤ 2^k) (v : Tapes commonCount prime) :
    step (Shared50RecursiveControl.program capacity width pcStack (implementation k))
      (entryConfig capacity .halt v) = none := by
  have hh : step (family capacity width pcStack (implementation k) (encoding .halt))
      ((raw v (tapeCount capacity width pcStack (implementation k))).start
        (family capacity width pcStack (implementation k) (encoding .halt))) = none := by
    unfold family states tapeCount
    rw [encoding.symm_apply_apply]
    exact SharedBankFamilyExact.pad_halt (skip commonCount prime (Nat.zero_lt_of_lt width.isLt))
      (SharedBankFamily.common_le_tapeCount (block capacity width pcStack (implementation k)))
      (le_refl commonCount) v 0 (by simp [step,skip,SharedBankFamilyExact.atState])
  have he : next capacity width pcStack (implementation k) (encoding .halt)
      (((raw v (tapeCount capacity width pcStack (implementation k))).start
        (family capacity width pcStack (implementation k) (encoding .halt))).state) = none := by
    unfold next states family tapeCount
    rw [encoding.symm_apply_apply]
    rfl
  exact FiniteFlow.halt (family capacity width pcStack (implementation k))
    (next capacity width pcStack (implementation k)) (encoding .guard) (encoding .halt) _ hh he

/-- A root-sentinel base invocation actually halts and returns the exact bank. -/
theorem graph_base_hoare (capacity : Fintype.card PC ≤ 2^k)
    (v : Descriptor) (hw : v.width=1) (hp : v.Positive)
    (roles : Tapes payloadCount prime) (old hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (aux : Tapes 0 prime) (st : Tapes 2 prime)
    (hd : RecursiveStackAllocation.Available 0 st)
    (hpc : RecursiveStackAllocation.Available 1 st)
    (x : Fin (volume prime v) → Fin 4) (hh : roles.head io=0)
    (ht : roles.tape io=RecursiveShiftRoleBank.source x) :
    HoareTime (Shared50RecursiveControl.program capacity width pcStack (implementation k))
      (fun w => w = raw (bank roles hs f p node scalar aux
        (RecursiveChildCallSetup.savedStacks old st (rootCode capacity)))
        (tapeCount capacity width pcStack (implementation k)))
      (fun w => w = raw (bank (RecursiveShiftRoleBank.updated roles io (RecursiveDigitRoleBank.array hw x))
        old f p node scalar aux st) (tapeCount capacity width pcStack (implementation k)))
      (RecursiveDigitRoleBank.coefficient*volume prime v+RecursiveChildCallReturn.cost old hs+k+7) := by
  intro w h
  subst w
  obtain ⟨n,hn,hr⟩ := guard_base_return capacity .halt v hw hp roles old hs hv f p node scalar aux st hd hpc x hh ht
  exact ⟨n,_,hn,hr,halt_entry capacity _,rfl⟩

/-- Complete execution of the fixed root program at width one, including root
initialization, the interchange, all return work and actual final halt. -/
theorem root_base_hoare (v : Descriptor) (hw : v.width=1) (hp : v.Positive)
    (roles : Tapes payloadCount prime) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (hd : RecursiveStackAllocation.Available 0 st)
    (hpc : RecursiveStackAllocation.Available 1 st)
    (x : Fin (volume prime v) → Fin 4) (hh : roles.head io=0)
    (ht : roles.tape io=RecursiveShiftRoleBank.source x) :
    HoareTime Shared50RecursiveImplementation.program
      (fun w => w = raw (bank roles hs f p node scalar (SharedBank.empty 0 prime) st)
        Shared50RecursiveRoot.tapeCount)
      (fun w => w = raw (bank (RecursiveShiftRoleBank.updated roles io (RecursiveDigitRoleBank.array hw x))
        hs f p node scalar (SharedBank.empty 0 prime) st) Shared50RecursiveRoot.tapeCount)
      (BinaryDescriptorFrames.cost Shared50RecursiveImplementation.rootFields (Shared50RecursiveRoot.words hs)+
        1+Shared50RecursiveImplementation.returnWidth+1+
        (RecursiveDigitRoleBank.coefficient*volume prime v+RecursiveChildCallReturn.cost hs hs+
          Shared50RecursiveImplementation.returnWidth+7)) :=
  Shared50RecursiveRoot.root_hoare roles hs f p node scalar st _ _
    (graph_base_hoare Shared50RecursiveImplementation.returnCapacity v hw hp roles hs hs hv
      f p node scalar (SharedBank.empty 0 prime) st hd hpc x hh ht)

def baseCoefficient : ℕ := RecursiveDigitRoleBank.coefficient+208+2*Shared50RecursiveImplementation.returnWidth

/-- Complete root base-case runtime is linear in its logical payload volume,
including both stack frames and all compiled controller transitions. -/
theorem root_base_linear (v : Descriptor) (hw : v.width=1) (hp : v.Positive)
    (roles : Tapes payloadCount prime) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (hd : RecursiveStackAllocation.Available 0 st)
    (hpc : RecursiveStackAllocation.Available 1 st)
    (x : Fin (volume prime v) → Fin 4) (hh : roles.head io=0)
    (ht : roles.tape io=RecursiveShiftRoleBank.source x) :
    HoareTime Shared50RecursiveImplementation.program
      (fun w => w = raw (bank roles hs f p node scalar (SharedBank.empty 0 prime) st)
        Shared50RecursiveRoot.tapeCount)
      (fun w => w = raw (bank (RecursiveShiftRoleBank.updated roles io (RecursiveDigitRoleBank.array hw x))
        hs f p node scalar (SharedBank.empty 0 prime) st) Shared50RecursiveRoot.tapeCount)
      (baseCoefficient*volume prime v) := by
  have hchild : RecursiveInterchangeLayout.child prime 1 1 v (0 : Fin 1) 0 = v := by
    cases v
    simp_all [RecursiveInterchangeLayout.child]
  have hreturn := RecursiveRoleChildCallSetup.restore_cost_le Shared50ModularControl.prime_prime.two_le
    1 v (0 : Fin 1) 0 (by simpa using hw) hp hs hs hv (by simpa only [hchild] using hv)
  have hsetup := Shared50RecursiveRoot.setup_cost_linear v hp hs hv
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hp
  apply (root_base_hoare v hw hp roles hs hv f p node scalar st hd hpc x hh ht).consequence
    (fun _ h => h) (fun _ h => h)
  unfold baseCoefficient
  nlinarith

end
end IntegerMultBounds.Machine.Shared50RecursiveBaseExecution
