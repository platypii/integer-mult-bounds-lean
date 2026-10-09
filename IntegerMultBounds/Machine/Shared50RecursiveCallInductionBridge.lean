import IntegerMultBounds.Machine.Shared50RecursiveCallReady

/-! Exact canonical-bank adapters for applying the recursive induction to an
actual entered call and returning to the physical recovery block. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveCallInductionBridge
noncomputable section
open Networks
open Shared50ModularControl (prime)
open Shared50GlobalBudget (World)
open Shared50NodeSegments (payloadCount io)
open Shared50NodePieceTransport (worldSlot)
open Shared50RecursiveCallLayout
open Shared50RecursiveCallSemantics (childRoles)
open Shared50RecursiveCallReady (parkedBank Ready)
open Shared50RecursiveBank (bank)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveRoleSerialization (roles)
open Shared50RecursiveNodeSemantics (encoded)
open Shared50RecursiveNodeLayout (wires)
open Shared50RecursiveChildPermutation (toChild array)
open SharedPlacementAlphabet (setTape)
variable {b k u : ℕ} {v : Descriptor}
attribute [local irreducible] Shared50RecursiveCallLayout.parked Shared50FixedControl.control
  Shared50GlobalCircuit.program50 Shared50Finite.program SharedPointReplay.circuit SharedPointExecution.code

theorem input_bank (w : World) (i j : Fin 125000) (hw : v.width=125000*b)
    (bits : World → Fin (volume prime v) → ZMod 2) (hs ch : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (aux : Tapes u prime) (st : Tapes 2 prime) :
    let mid := parkedBank w bits hs f p node scalar aux st
    ∀ st' : Tapes 2 prime,
      RecursiveCallProtocol.childBank mid ch (node.append (scalar.append aux)) st' =
      bank (roles (RecursiveRowsSerialization.sourceData wires (encoded (toChild hw i j (bits w))))) ch
        (mid.tape (RecursiveCallBank.controlSlot 2)) (mid.head (RecursiveCallBank.controlSlot 2)) node scalar aux st'  := by
  dsimp only
  intro st'
  have hmid : RecursiveCallProtocol.entered (parked w) (worldSlot w) io (volume prime v)
      (bank (roles (Shared50NodeGates.encoded bits (fun _ => blank))) hs f p node scalar aux st) =
      parkedBank w bits hs f p node scalar aux st := rfl
  have hrole0 := Shared50RecursiveCallSemantics.entered_rolePart w (volume prime v)
    (bank (roles (Shared50NodeGates.encoded bits (fun _ => blank))) hs f p node scalar aux st)
  have hrole := ((congrArg RecursiveCallBank.rolePart hmid).symm.trans hrole0).trans
    (congrArg childRoles (Shared50RecursiveCallReady.parent_source w bits hs f p node scalar aux st))
  have hx : RecursiveShiftRoleBank.source (encoded (toChild hw i j (bits w))) =
      RecursiveShiftRoleBank.source (encoded (bits w)) :=
    Shared50RecursiveChildPermutation.toChild_source hw i j (encoded (bits w))
  have hroles : roles (RecursiveRowsSerialization.sourceData wires (encoded (toChild hw i j (bits w)))) =
      childRoles (RecursiveShiftRoleBank.source (encoded (bits w))) :=
    (Shared50RecursiveCallReady.source_roles _).trans (congrArg childRoles hx)
  exact congrArg (fun rr => RecursiveCallBank.bank rr ch
    ((parkedBank w bits hs f p node scalar aux st).tape (RecursiveCallBank.controlSlot 2))
    ((parkedBank w bits hs f p node scalar aux st).head (RecursiveCallBank.controlSlot 2))
    (node.append (scalar.append aux)) st') (hrole.trans hroles.symm)

/-- The canonical returned child word is precisely the IO update required by
physical recovery, with original parent headers and return stacks restored. -/
theorem returned_word (w : World) (bits : World → Fin (volume prime v) → ZMod 2)
    (hs : Fin 6 → List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (node scalar : Tapes 1 prime) (aux : Tapes u prime) (st : Tapes 2 prime)
    (out : ℤ → Fin (prime+4)) :
    let mid := parkedBank w bits hs f p node scalar aux st
    bank (childRoles out) hs (mid.tape (RecursiveCallBank.controlSlot 2))
      (mid.head (RecursiveCallBank.controlSlot 2)) node scalar aux st =
      setTape mid (RecursiveCallBank.role (u := 1+(1+u)) io).val out 0 := by
  let rr := roles (Shared50NodeGates.encoded bits (fun _ => blank))
  let vv := bank rr hs f p node scalar aux st
  have hbank := RecursiveCallBank.entered_bank (parked w) (worldSlot w) io (volume prime v)
    rr hs f p (node.append (scalar.append aux)) st
  have hmid : RecursiveCallProtocol.entered (parked w) (worldSlot w) io (volume prime v)
      (RecursiveCallBank.bank rr hs f p (node.append (scalar.append aux)) st) =
      parkedBank w bits hs f p node scalar aux st := rfl
  have hbank' := Eq.mp (congrArg (fun mid => mid = RecursiveCallBank.bank (RecursiveCallBank.rolePart mid)
    hs (mid.tape (RecursiveCallBank.controlSlot 2)) (mid.head (RecursiveCallBank.controlSlot 2))
    (node.append (scalar.append aux)) st) hmid) hbank
  have hroles := Shared50RecursiveCallSemantics.entered_rolePart w (volume prime v) vv
  have hroles' := (congrArg RecursiveCallBank.rolePart hmid).symm.trans hroles
  have hupdate : setTape (RecursiveCallBank.rolePart (parkedBank w bits hs f p node scalar aux st)) io out 0 =
      childRoles out := by
    exact (congrArg (fun rr => setTape rr io out 0) hroles').trans
      (SharedPlacementAlphabet.setTape_setTape (SharedBank.empty payloadCount prime) io _ out 0 0)
  have hup := Shared50RecursiveCallSemantics.bank_setTape
    (RecursiveCallBank.rolePart (parkedBank w bits hs f p node scalar aux st)) hs
    ((parkedBank w bits hs f p node scalar aux st).tape (RecursiveCallBank.controlSlot 2))
    ((parkedBank w bits hs f p node scalar aux st).head (RecursiveCallBank.controlSlot 2))
    (node.append (scalar.append aux)) st io out
  exact (congrArg (fun rr => RecursiveCallBank.bank rr hs
    ((parkedBank w bits hs f p node scalar aux st).tape (RecursiveCallBank.controlSlot 2))
    ((parkedBank w bits hs f p node scalar aux st).head (RecursiveCallBank.controlSlot 2))
    (node.append (scalar.append aux)) st) hupdate.symm).trans
      (hup.trans (congrArg (fun mid => setTape mid (RecursiveCallBank.role (u := 1+(1+u)) io).val out 0) hbank'.symm))

theorem returned_bank (w : World) (i j : Fin 125000) (hw : v.width=125000*b)
    (bits : World → Fin (volume prime v) → ZMod 2) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (aux : Tapes u prime) (st : Tapes 2 prime) :
    let mid := parkedBank w bits hs f p node scalar aux st
    bank (roles (RecursiveRowsSerialization.sourceData wires
      (encoded (Shared50RecursiveNodeRows.transpose (one_dvd _) (toChild hw i j (bits w)))))) hs
      (mid.tape (RecursiveCallBank.controlSlot 2)) (mid.head (RecursiveCallBank.controlSlot 2)) node scalar aux st =
      setTape mid (RecursiveCallBank.role (u := 1+(1+u)) io).val
        (RecursiveShiftRoleBank.source (array hw i j (encoded (bits w)))) 0 := by
  have hx : RecursiveShiftRoleBank.source
      (encoded (Shared50RecursiveNodeRows.transpose (one_dvd _) (toChild hw i j (bits w)))) =
      RecursiveShiftRoleBank.source (array hw i j (encoded (bits w))) :=
    Shared50RecursiveChildPermutation.return_source hw i j (encoded (bits w))
  have hroles := (Shared50RecursiveCallReady.source_roles
    (encoded (Shared50RecursiveNodeRows.transpose (one_dvd _) (toChild hw i j (bits w))))).trans
      (congrArg childRoles hx)
  exact (congrArg (fun rr => bank rr hs
    ((parkedBank w bits hs f p node scalar aux st).tape (RecursiveCallBank.controlSlot 2))
    ((parkedBank w bits hs f p node scalar aux st).head (RecursiveCallBank.controlSlot 2)) node scalar aux st) hroles).trans
      (returned_word w bits hs f p node scalar aux st _)

/-- The induction stack premise is automatic for every constructed child header. -/
theorem ready (w : World) (bits : World → Fin (volume prime v) → ZMod 2)
    (hs : Fin 6 → List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (node scalar : Tapes 1 prime) (aux : Tapes u prime) (st : Tapes 2 prime)
    (code : FiniteReturnStack.Code k) (hr : Ready f p node scalar st) :
    let mid := parkedBank w bits hs f p node scalar aux st
    Ready (mid.tape (RecursiveCallBank.controlSlot 2)) (mid.head (RecursiveCallBank.controlSlot 2))
      node scalar (RecursiveChildCallSetup.savedStacks hs st code) := by
  have hf := Shared50RecursiveCallSemantics.entered_bank_blank_suffix w (volume prime v)
    (roles (Shared50NodeGates.encoded bits (fun _ => blank))) hs f p (node.append (scalar.append aux)) st hr.payload
  have hmid : RecursiveCallProtocol.entered (parked w) (worldSlot w) io (volume prime v)
      (RecursiveCallBank.bank (roles (Shared50NodeGates.encoded bits (fun _ => blank))) hs f p
        (node.append (scalar.append aux)) st) = parkedBank w bits hs f p node scalar aux st := rfl
  have hfp := Eq.mp (congrArg (fun vv : Tapes (Shared50RecursiveBank.Count payloadCount u) prime =>
    ∀ z, vv.head (RecursiveCallBank.controlSlot 2) ≤ z → vv.tape (RecursiveCallBank.controlSlot 2) z = blank) hmid) hf
  have hst := RecursiveStackAllocation.saved_stacks_available hs st code hr.descriptor hr.pc
  exact ⟨hfp,hr.node,hr.scalar,hst.1,hst.2⟩


/-- The child contract itself adds its saved frame; its pre-save stack premise
uses the unchanged original descriptor and PC stack banks. -/
theorem ready_original (w : World) (bits : World → Fin (volume prime v) → ZMod 2)
    (hs : Fin 6 → List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (node scalar : Tapes 1 prime) (aux : Tapes u prime) (st : Tapes 2 prime)
    (hr : Ready f p node scalar st) :
    let mid := parkedBank w bits hs f p node scalar aux st
    Ready (mid.tape (RecursiveCallBank.controlSlot 2)) (mid.head (RecursiveCallBank.controlSlot 2))
      node scalar st := by
  have hf := Shared50RecursiveCallSemantics.entered_bank_blank_suffix w (volume prime v)
    (roles (Shared50NodeGates.encoded bits (fun _ => blank))) hs f p (node.append (scalar.append aux)) st hr.payload
  have hmid : RecursiveCallProtocol.entered (parked w) (worldSlot w) io (volume prime v)
      (RecursiveCallBank.bank (roles (Shared50NodeGates.encoded bits (fun _ => blank))) hs f p
        (node.append (scalar.append aux)) st) = parkedBank w bits hs f p node scalar aux st := rfl
  have hfp := Eq.mp (congrArg (fun vv : Tapes (Shared50RecursiveBank.Count payloadCount u) prime =>
    ∀ z, vv.head (RecursiveCallBank.controlSlot 2) ≤ z → vv.tape (RecursiveCallBank.controlSlot 2) z = blank) hmid) hf
  exact ⟨hfp,hr.node,hr.scalar,hr.descriptor,hr.pc⟩

end
end IntegerMultBounds.Machine.Shared50RecursiveCallInductionBridge
