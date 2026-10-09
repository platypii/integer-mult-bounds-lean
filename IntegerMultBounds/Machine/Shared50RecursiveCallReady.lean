import IntegerMultBounds.Machine.Shared50RecursiveCallRecovery
import IntegerMultBounds.Machine.Shared50RecursiveChildPermutation
import IntegerMultBounds.Machine.Shared50RecursiveBank
import IntegerMultBounds.Machine.RecursiveStackAllocation

/-! Actual recursive call entry automatically supplies the canonical binary
child input and all available-stack invariants. The child headers are those
constructed by the physical entry block, not an externally initialized bank. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveCallReady
noncomputable section
open Networks
open Shared50ModularControl (prime)
open Shared50GlobalBudget (World)
open Shared50TapeGlobal (roleCount roleEquiv)
open Shared50NodeSegments (payloadCount io)
open Shared50NodePieceTransport (worldSlot)
open Shared50RecursiveCallLayout
open Shared50RecursiveCallSemantics (childRoles)
open Shared50RecursiveBank (bank)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveRoleSerialization (roles)
open SharedBankStageInput (raw)
open RecursiveStackAllocation (Available)
open Shared50RecursiveNodeSemantics (encoded)
open Shared50RecursiveChildPermutation (toChild)
variable {b k u : ℕ} {v : Descriptor}
attribute [local irreducible] Shared50RecursiveCallLayout.parked Shared50FixedControl.control
  Shared50GlobalCircuit.program50 Shared50Finite.program SharedPointReplay.circuit SharedPointExecution.code

/-- Recursive stacks have unbounded blank suffixes at their actual heads;
scalar view work starts blank, while older node-view frames remain allowed. -/
structure Ready (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (st : Tapes 2 prime) : Prop where
  payload : ∀ z, p ≤ z → f z = blank
  node : Available 0 node
  scalar : scalar = SharedBank.empty 1 prime
  descriptor : Available 0 st
  pc : Available 1 st

/-- The canonical node input serialization is exactly blank World slots plus
its sole I/O word, even when the word contains blank or separator symbols. -/
theorem source_roles (x : Fin (volume prime v) → Fin 4) :
    roles (RecursiveRowsSerialization.sourceData Shared50RecursiveNodeLayout.wires x) =
      childRoles (RecursiveShiftRoleBank.source x) := by
  have hx (j : Fin roleCount) :
      RecursiveRowsSerialization.sourceData Shared50RecursiveNodeLayout.wires x (Fin.castAdd 1 j) = fun _ => blank := by
    rw [← Shared50RecursiveNodeLayout.wires_role]
    change RecursiveRowsSerialization.putData _ _ _ = _
    rw [RecursiveRowsSerialization.putData_selected _ Shared50RecursiveNodeLayout.wires_injective]
    simp only [RecursiveRowsSerialization.sourceLocal,Fin.addCases_right]
  have hi : RecursiveRowsSerialization.sourceData Shared50RecursiveNodeLayout.wires x io = x := by
    change RecursiveRowsSerialization.putData _ _ (Shared50RecursiveNodeLayout.wires (Fin.castAdd roleCount (0 : Fin 1))) = x
    rw [RecursiveRowsSerialization.putData_selected _ Shared50RecursiveNodeLayout.wires_injective]
    simp only [RecursiveRowsSerialization.sourceLocal,Fin.addCases_left]
  apply congrArg₂ Tapes.mk
  · funext j
    simp only [SharedBank.empty]
    exact (Function.update_eq_self io (fun _ => (0 : ℤ))).symm ▸ rfl
  · funext j
    induction j using Fin.addCases with
    | left j =>
      have hn : Fin.castAdd 1 j ≠ io := by
        simpa only [worldSlot,Equiv.symm_apply_apply] using active_ne_io (roleEquiv j)
      simp only [SharedBank.empty,Function.update_of_ne hn,hx]
      exact RecursiveRowsSerialization.source_blank v
    | right j =>
      have he : Fin.natAdd roleCount j = io := by
        apply Fin.ext; have hj := j.isLt; simp only [io,Fin.val_natAdd,Fin.val_last]; omega
      rw [he]
      simp only [Function.update_self,hi]

/-- The exact intermediate bank produced by actual payload parking and move. -/
def parkedBank (w : World) (bits : World → Fin (volume prime v) → ZMod 2)
    (hs : Fin 6 → List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (node scalar : Tapes 1 prime) (aux : Tapes u prime) (st : Tapes 2 prime) :=
  RecursiveCallProtocol.entered (parked w) (worldSlot w) io (volume prime v)
    (bank (roles (Shared50NodeGates.encoded bits (fun _ => blank))) hs f p node scalar aux st)

/-- Exact active source in the original bank, with the existing World naming. -/
theorem parent_source (w : World) (bits : World → Fin (volume prime v) → ZMod 2)
    (hs : Fin 6 → List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (node scalar : Tapes 1 prime) (aux : Tapes u prime) (st : Tapes 2 prime) :
    (bank (roles (Shared50NodeGates.encoded bits (fun _ => blank))) hs f p node scalar aux st).tape
      (RecursiveCallBank.role (worldSlot w)).val = RecursiveShiftRoleBank.source (encoded (bits w)) := by
  simp only [bank,RecursiveCallBank.bank,RecursiveShiftRoleBank.common,RecursiveCallBank.role,
    Tapes.append,Fin.addCases_left,roles]
  exact congrArg RecursiveShiftRoleBank.source (funext fun z => Shared50NodePieceTransport.encoded_entry bits _ w z)

/-- Constructed child headers, actual canonical binary input, and all nested
allocation invariants from the actual entry program. Auxiliary node/scalar
tapes are literally retained, including all older node frames. -/
theorem enters (w : World) (i j : Fin 125000) (hw : v.width=125000*b)
    (bits : World → Fin (volume prime v) → ZMod 2) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (aux : Tapes u prime) (st : Tapes 2 prime) (code : FiniteReturnStack.Code k)
    (hr : Ready f p node scalar st) :
    let mid := parkedBank w bits hs f p node scalar aux st
    ∃ ch : Fin 6 → List Bool,
      RecursiveDimensionBank.Headers (RecursiveAffineViews.cross prime b v i j) ch ∧
      (RecursiveAffineViews.cross prime b v i j).Positive ∧
      Ready (mid.tape (RecursiveCallBank.controlSlot 2)) (mid.head (RecursiveCallBank.controlSlot 2))
        node scalar (RecursiveChildCallSetup.savedStacks hs st code) ∧
      HoareTime (RecursiveCallProtocol.enter (u := 1+(1+u)) (parked w) (worldSlot w) io (active_ne_io w) i j code).program
        (fun ww => ww = raw (bank (roles (Shared50NodeGates.encoded bits (fun _ => blank))) hs f p node scalar aux st)
          (RecursiveCallProtocol.enter (u := 1+(1+u)) (parked w) (worldSlot w) io (active_ne_io w) i j code).tapes)
        (fun ww => ww = raw (bank
          (roles (RecursiveRowsSerialization.sourceData Shared50RecursiveNodeLayout.wires (encoded (toChild hw i j (bits w)))))
          ch (mid.tape (RecursiveCallBank.controlSlot 2)) (mid.head (RecursiveCallBank.controlSlot 2))
          node scalar aux (RecursiveChildCallSetup.savedStacks hs st code))
          (RecursiveCallProtocol.enter (u := 1+(1+u)) (parked w) (worldSlot w) io (active_ne_io w) i j code).tapes)
        ((88*(parked w).length+51884+RecursiveRoleChildCallSetup.constant 125000 k)*volume prime v) := by
  dsimp only
  obtain ⟨ch,hch,he⟩ := RecursiveCallProtocol.enters (parked w) (parked_nodup w) (worldSlot w) io
    (active_ne_io w) (active_not_parked w) (io_not_parked w) b v i j hw (roles (Shared50NodeGates.encoded bits (fun _ => blank)))
    hs f p (node.append (scalar.append aux)) st code hv hp
    (fun z _ => Shared50RecursiveCallSemantics.roles_supported (Shared50NodeGates.encoded bits (fun _ => blank)) z)
    (Shared50RecursiveCallSemantics.roles_supported (Shared50NodeGates.encoded bits (fun _ => blank)) (worldSlot w)) (by
      constructor
      · rfl
      · change RecursiveShiftRoleBank.source ((Shared50NodeGates.encoded bits (fun _ => blank)) io) = _
        have hi : io = Fin.natAdd roleCount (0 : Fin 1) := by apply Fin.ext; simp [io]
        simp only [Shared50NodeGates.encoded,Shared50NodeGates.extend,hi,Fin.addCases_right]
        exact RecursiveRowsSerialization.source_blank v)
  have hst := RecursiveStackAllocation.saved_stacks_available hs st code hr.descriptor hr.pc
  have hf := Shared50RecursiveCallSemantics.entered_bank_blank_suffix w (volume prime v)
    (roles (Shared50NodeGates.encoded bits (fun _ => blank))) hs f p (node.append (scalar.append aux)) st hr.payload
  have hmid : RecursiveCallProtocol.entered (parked w) (worldSlot w) io (volume prime v)
      (RecursiveCallBank.bank (roles (Shared50NodeGates.encoded bits (fun _ => blank))) hs f p
        (node.append (scalar.append aux)) st) = parkedBank w bits hs f p node scalar aux st := rfl
  have hfp := Eq.mp (congrArg (fun vv : Tapes (Shared50RecursiveBank.Count payloadCount u) prime =>
    ∀ z, vv.head (RecursiveCallBank.controlSlot 2) ≤ z → vv.tape (RecursiveCallBank.controlSlot 2) z = blank) hmid) hf
  refine ⟨ch,hch,RecursiveInterchangeLayout.child_positive prime 1 b v i j
    Shared50ModularControl.prime_prime.pos (by decide) (one_dvd _) hp,
    ⟨hfp,hr.node,hr.scalar,hst.1,hst.2⟩,?_⟩
  have hx : RecursiveShiftRoleBank.source (encoded (toChild hw i j (bits w))) =
      RecursiveShiftRoleBank.source (encoded (bits w)) :=
    Shared50RecursiveChildPermutation.toChild_source hw i j (encoded (bits w))
  have hrole0 := Shared50RecursiveCallSemantics.entered_rolePart w (volume prime v)
    (bank (roles (Shared50NodeGates.encoded bits (fun _ => blank))) hs f p node scalar aux st)
  have hrole := ((congrArg RecursiveCallBank.rolePart hmid).symm.trans hrole0).trans
    (congrArg childRoles (parent_source w bits hs f p node scalar aux st))
  have hroles : roles (RecursiveRowsSerialization.sourceData Shared50RecursiveNodeLayout.wires
      (encoded (toChild hw i j (bits w)))) = childRoles (RecursiveShiftRoleBank.source (encoded (bits w))) :=
    (source_roles _).trans (congrArg childRoles hx)
  have hend := congrArg (fun rr => RecursiveCallBank.bank rr ch
    ((parkedBank w bits hs f p node scalar aux st).tape (RecursiveCallBank.controlSlot 2))
    ((parkedBank w bits hs f p node scalar aux st).head (RecursiveCallBank.controlSlot 2))
    (node.append (scalar.append aux)) (RecursiveChildCallSetup.savedStacks hs st code))
      (hrole.trans hroles.symm)
  have heq := (congrArg (fun mid => RecursiveCallProtocol.childBank mid ch
    (node.append (scalar.append aux)) (RecursiveChildCallSetup.savedStacks hs st code)) hmid).trans hend
  apply he.consequence (fun _ h => h) _ le_rfl
  intro ww hww
  exact hww.trans (congrArg (fun vv => raw vv
    (RecursiveCallProtocol.enter (u := 1+(1+u)) (parked w) (worldSlot w) io (active_ne_io w) i j code).tapes) heq)

end
end IntegerMultBounds.Machine.Shared50RecursiveCallReady
