import IntegerMultBounds.Machine.Shared50RecursivePieceExecution
import IntegerMultBounds.Machine.Shared50RecursiveNodePieces

/-! A recursive node's real split, literal binary schedule, merge, ancestor
header restoration and decoded return execute on one fixed cyclic graph.
Only recursive child graph traces remain premises. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveNodeExecution
noncomputable section
open Networks
open Shared50ModularControl (prime)
open Shared50GlobalBudget (World)
open Shared50TapeGlobal (roleCount)
open Shared50RecursiveControl
open Shared50RecursiveImplementation (commonCount implementation width pcStack)
open Shared50RecursiveBaseExecution (entryConfig)
open Shared50RecursivePieceExecution (dataBank actualCallBound overhead)
open Shared50RecursiveNodeLayout (wires wires_injective mergeRoute)
open Shared50RecursiveNodeSemantics (encoded)
open RecursiveInterchangeLayout (Descriptor volume role)
open RecursiveViewedAction (Data)
open Shared50NodeSegments (payloadCount)
open SharedBankStageInput (raw)
variable {k b : ℕ} {v : Descriptor}
attribute [local irreducible] Shared50PieceSchedule.pieces Shared50FixedControl.control

/-- Exactly the remaining child trace obligation at each reachable binary
call boundary. Its budget includes the physical entry and recovery work. -/
def Calls (capacity : Fintype.card PC ≤ 2^k) (hw : v.width=125000*b)
    (hs : Fin 6 → List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (node : Tapes 1 prime) (st : Tapes 2 prime) (C : ℕ) : Prop :=
  ∀ (site : Site) w i j, Shared50PieceSchedule.pieces[site] = .call w i j →
    ∀ data : Data payloadCount v, Shared50RecursiveBinaryInvariant.Ready data →
      ∃ n ≤ actualCallBound (v := v) k C w i j,
        Machine.run (Shared50RecursiveControl.program capacity width pcStack (implementation k)) n
          (entryConfig capacity (.piece site) (dataBank hs f p node st data)) =
        some (entryConfig capacity (successor site) (dataBank hs f p node st
          (Shared50RecursiveChildPermutation.child hw w i j data)))

def entryCoefficient : ℕ :=
  74+RecursiveRowsNode.rowConstant roleCount+RecursiveRowsNodeRoleBank.constant roleCount
def exitCoefficient : ℕ := 128+RecursiveRowsNode.rowConstant roleCount

theorem split_block (capacity : Fintype.card PC ≤ 2^k) :
    block capacity width pcStack (implementation k) .split =
      Shared50RecursiveBankNodes.entry (u := 0) wires wires_injective := rfl

theorem merge_block (capacity : Fintype.card PC ≤ 2^k) :
    block capacity width pcStack (implementation k) .merge =
      Shared50RecursiveBankNodes.exit (u := 0) mergeRoute wires wires_injective := rfl

/-- Shared restoration and exact decoded return, independent of the completed
node's payload array. This keeps framed stack reduction outside node assembly. -/
theorem restore_return (capacity : Fintype.card PC ≤ 2^k) (target : PC)
    (roles : Tapes payloadCount prime) (old hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime) (st : Tapes 2 prime)
    (hd : RecursiveStackAllocation.Available 0 st) (hpc : RecursiveStackAllocation.Available 1 st) :
    ∃ steps ≤ RecursiveChildCallReturn.cost old hs+k+3,
      Machine.run (Shared50RecursiveControl.program capacity width pcStack (implementation k)) steps
        (entryConfig capacity .restore (Shared50RecursiveBank.bank roles hs f p node
          (SharedBank.empty 1 prime) (SharedBank.empty 0 prime)
          (RecursiveChildCallSetup.savedStacks old st (FiniteReturnStack.address capacity (encoding target))))) =
        some (entryConfig capacity target (Shared50RecursiveBank.bank roles old f p node
          (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) st)) := by
  let code := FiniteReturnStack.address capacity (encoding target)
  let before := Shared50RecursiveBank.bank roles hs f p node (SharedBank.empty 1 prime)
    (SharedBank.empty 0 prime) (RecursiveChildCallSetup.savedStacks old st code)
  let pending := Shared50RecursiveBank.bank roles old f p node (SharedBank.empty 1 prime)
    (SharedBank.empty 0 prime) (RecursiveChildCallReturn.pending st code)
  let after := Shared50RecursiveBank.bank roles old f p node (SharedBank.empty 1 prime)
    (SharedBank.empty 0 prime) st
  have hrestore := Shared50RecursiveBankReturn.restore_hoare roles old hs f p node
    (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) st code hd
  obtain ⟨nr,hnr,hrr⟩ := Shared50RecursiveBlockExecution.block_jump capacity width pcStack
    (implementation k) .restore .pop before pending (RecursiveChildCallReturn.cost old hs) hrestore (fun _ => rfl)
  obtain ⟨hhead,htape⟩ := Shared50RecursiveBankReturn.pending_pc roles
    old f p node (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) st code
  have hfree : ∀ j < k, st.tape 1 (st.head 1+j)=blank := RecursiveStackAllocation.pc_free 1 st hpc
  have hpop := Shared50RecursiveReturnExecution.pop_jump capacity width pcStack (implementation k)
    target pending (st.tape 1) (st.head 1) htape hhead hfree
  have hreset : SharedPlacementAlphabet.setTape pending pcStack (st.tape 1) (st.head 1) = after :=
    Shared50RecursiveBankReturn.reset_pending roles old f p node
      (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) st code
  rw [hreset] at hpop
  change Machine.run _ nr (entryConfig capacity .restore before) = some (entryConfig capacity .pop pending) at hrr
  change Machine.run _ (k+2) (entryConfig capacity .pop pending) = some (entryConfig capacity target after) at hpop
  refine ⟨nr+(k+2),by omega,?_⟩
  rw [run_add,hrr,Option.bind_some]
  exact hpop

/-- Generic graph entry keeps the role count symbolic during kernel checking. -/
def graphConfig {t : ℕ} (capacity : Fintype.card PC ≤ 2^k) (width stack : Fin t)
    (impl : Implementation t prime k) (pc : PC) (bank : Tapes t prime) :=
  ((raw bank (tapeCount capacity width stack impl)).start
    (family capacity width stack impl (encoding pc))).mapState
      (FiniteFlow.embed (states capacity width stack impl) (encoding pc))

/-- Physical split execution proved with a symbolic role count. Specializing
this theorem never asks the kernel to enumerate the fixed World role bank. -/
theorem entry_run_general {t c : ℕ} (capacity : Fintype.card PC ≤ 2^k)
    (width stack : Fin (Shared50RecursiveBank.Count t 0))
    (impl : Implementation (Shared50RecursiveBank.Count t 0) prime k)
    (wires : Fin (1+c) → Fin t) (hwires : Function.Injective wires)
    (hblock : impl.split = Shared50RecursiveBankNodes.entry (u := 0) wires hwires)
    (hc : 0 < c) (hp : v.Positive) (hdiv : c ∣ v.rows) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (node : Tapes 1 prime) (st : Tapes 2 prime) (x : Fin (volume prime v) → Fin 4) :
    ∃ rs : List Bool, RecursiveDimensionBank.Headers (role v c) (RecursiveRowsNodeHeaders.headers hs rs) ∧
      ∃ n ≤ (74+RecursiveRowsNode.rowConstant c+RecursiveRowsNodeRoleBank.constant c)*volume prime v+1,
        Machine.run (Shared50RecursiveControl.program capacity width stack impl) n
          (graphConfig capacity width stack impl .split (Shared50RecursiveBank.bank
            (RecursiveRoleSerialization.roles (RecursiveRowsSerialization.sourceData wires x)) hs f p node
            (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) st)) =
          some (graphConfig capacity width stack impl first (Shared50RecursiveBank.bank
            (RecursiveRoleSerialization.roles (RecursiveRowsSerialization.roleData wires (Equiv.refl _) hdiv x))
            (RecursiveRowsNodeHeaders.headers hs rs) f p (RecursiveViewFrame.savedStack hs node)
            (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) st)) := by
  obtain ⟨rs,hrs,hentry⟩ := Shared50RecursiveBankNodes.entry_hoare wires hwires hs node
    (SharedBank.empty 1 prime) f p (SharedBank.empty 0 prime) st v hc hv hp hdiv x
  have heLinear := hentry.consequence (fun _ h => h) (fun _ h => h)
    (RecursiveRowsNode.entry_cost_linear (c := c) v hp hs hv)
  have hb : HoareTime (block capacity width stack impl .split).program
      (fun ww => ww = raw (Shared50RecursiveBank.bank
        (RecursiveRoleSerialization.roles (RecursiveRowsSerialization.sourceData wires x)) hs f p node
        (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) st) (block capacity width stack impl .split).tapes)
      (fun ww => ww = raw (Shared50RecursiveBank.bank
        (RecursiveRoleSerialization.roles (RecursiveRowsSerialization.roleData wires (Equiv.refl _) hdiv x))
        (RecursiveRowsNodeHeaders.headers hs rs) f p (RecursiveViewFrame.savedStack hs node)
        (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) st) (block capacity width stack impl .split).tapes)
      ((74+RecursiveRowsNode.rowConstant c+RecursiveRowsNodeRoleBank.constant c)*volume prime v) := by
    rw [block,hblock]
    exact heLinear
  obtain ⟨n,hn,hr⟩ := Shared50RecursiveBlockExecution.block_jump capacity width stack
    impl .split first _ _ _ hb (fun _ => rfl)
  exact ⟨rs,hrs,n,hn,hr⟩

/-- Generic physical merge trace, likewise with a symbolic finite role bank. -/
theorem merge_run_general {t c : ℕ} (capacity : Fintype.card PC ≤ 2^k)
    (width stack : Fin (Shared50RecursiveBank.Count t 0))
    (impl : Implementation (Shared50RecursiveBank.Count t 0) prime k)
    (rho : Equiv.Perm (Fin c)) (wires : Fin (1+c) → Fin t) (hwires : Function.Injective wires)
    (hblock : impl.merge = Shared50RecursiveBankNodes.exit (u := 0) rho wires hwires)
    (hc : 0 < c) (hp : v.Positive) (hdiv : c ∣ v.rows) (hs reduced : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (hrs : RecursiveDimensionBank.Headers (role v c) reduced)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime) (st : Tapes 2 prime)
    (hn : RecursiveStackAllocation.Available 0 node) (x : Fin (volume prime v) → Fin 4) :
    ∃ n ≤ (128+RecursiveRowsNode.rowConstant c)*volume prime v+1,
      Machine.run (Shared50RecursiveControl.program capacity width stack impl) n
        (graphConfig capacity width stack impl .merge (Shared50RecursiveBank.bank
          (RecursiveRoleSerialization.roles (RecursiveRowsSerialization.roleData wires rho hdiv x))
          reduced f p (RecursiveViewFrame.savedStack hs node) (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) st)) =
        some (graphConfig capacity width stack impl .restore (Shared50RecursiveBank.bank
          (RecursiveRoleSerialization.roles (RecursiveRowsSerialization.sourceData wires x)) hs f p node
          (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) st)) := by
  have hexit := Shared50RecursiveBankNodes.exit_hoare rho wires hwires hs reduced node
    (SharedBank.empty 1 prime) f p (SharedBank.empty 0 prime) st
    (RecursiveRowsNode.free_of_available hs node hn) v hc hv hp hdiv x
  have hb : HoareTime (block capacity width stack impl .merge).program
      (fun ww => ww = raw (Shared50RecursiveBank.bank
        (RecursiveRoleSerialization.roles (RecursiveRowsSerialization.roleData wires rho hdiv x))
        reduced f p (RecursiveViewFrame.savedStack hs node) (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) st)
        (block capacity width stack impl .merge).tapes)
      (fun ww => ww = raw (Shared50RecursiveBank.bank
        (RecursiveRoleSerialization.roles (RecursiveRowsSerialization.sourceData wires x)) hs f p node
        (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) st) (block capacity width stack impl .merge).tapes)
      ((128+RecursiveRowsNode.rowConstant c)*volume prime v) := by
    rw [block,hblock]
    exact hexit.consequence (fun _ h => h) (fun _ h => h)
      (RecursiveRowsNode.exit_cost_linear v hp hc hdiv hs reduced hv hrs)
  exact Shared50RecursiveBlockExecution.block_jump capacity width stack impl .merge .restore _ _ _ hb (fun _ => rfl)

/-- The actual split controller edge on a generic spectator stack bank. -/
theorem entry_run (capacity : Fintype.card PC ≤ 2^k) (hp : v.Positive)
    (hdiv : roleCount ∣ v.rows) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (node : Tapes 1 prime) (st : Tapes 2 prime) (x : Fin (volume prime v) → Fin 4) :
    ∃ rs : List Bool, RecursiveDimensionBank.Headers (role v roleCount)
        (RecursiveRowsNodeHeaders.headers hs rs) ∧
      ∃ n ≤ (74+RecursiveRowsNode.rowConstant roleCount+RecursiveRowsNodeRoleBank.constant roleCount)*volume prime v+1,
        Machine.run (Shared50RecursiveControl.program capacity width pcStack (implementation k)) n
          (entryConfig capacity .split (dataBank hs f p node st
            (RecursiveRowsSerialization.sourceData wires x))) =
          some (entryConfig capacity first (dataBank (RecursiveRowsNodeHeaders.headers hs rs) f p
            (RecursiveViewFrame.savedStack hs node) st
            (RecursiveRowsSerialization.roleData wires (Equiv.refl _) hdiv x))) := by
  exact entry_run_general capacity width pcStack (implementation k) wires wires_injective rfl
    (by decide) hp hdiv hs hv f p node st x

/-- Actual merge consumes the exact literal piece result. All descriptor and
PC stacks remain generic spectators of this local trace. -/
theorem merge_run (capacity : Fintype.card PC ≤ 2^k) (hw : v.width=125000*b)
    (hp : v.Positive) (hdiv : roleCount ∣ v.rows) (hs reduced : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs)
    (hrs : RecursiveDimensionBank.Headers (role v roleCount) reduced)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime) (st : Tapes 2 prime)
    (hn : RecursiveStackAllocation.Available 0 node) (x : Fin (volume prime v) → ZMod 2) :
    ∃ n ≤ (128+RecursiveRowsNode.rowConstant roleCount)*volume prime v+1,
      Machine.run (Shared50RecursiveControl.program capacity width pcStack (implementation k)) n
        (entryConfig capacity .merge (dataBank reduced f p (RecursiveViewFrame.savedStack hs node) st
          (Shared50NodePieceTransport.run (v := role v roleCount) hw
            (Shared50RecursiveChildPermutation.child (v := role v roleCount) hw) Shared50PieceSchedule.pieces
            (RecursiveRowsSerialization.roleData wires (Equiv.refl _) hdiv (encoded x))))) =
        some (entryConfig capacity .restore (dataBank hs f p node st
          (RecursiveRowsSerialization.sourceData wires (Shared50RecursiveNodeRows.transpose hdiv (encoded x))))) := by
  have hnetwork := (Shared50RecursiveNodePieces.run_network hw hdiv
    (Shared50RecursiveChildPermutation.child (v := role v roleCount) hw)
    (Shared50RecursiveChildPermutation.child_spec (v := role v roleCount) hw) x).trans
      (Shared50RecursiveNodeSemantics.networkData_merge_input hw hdiv x)
  rw [hnetwork]
  exact merge_run_general capacity width pcStack (implementation k) mergeRoute wires wires_injective rfl
    (by decide) hp hdiv hs reduced hv hrs f p node st hn (Shared50RecursiveNodeRows.transpose hdiv (encoded x))

/-- Arithmetic assembly is checked before the enormous fixed machine
coefficients are instantiated. No closed role-count circuit is evaluated. -/
theorem assembly_bound {E X V T R k ne ns nm nr : ℕ}
    (he : ne ≤ E*V+1) (hs : ns ≤ T) (hm : nm ≤ X*V+1) (hr : nr ≤ R+k+3) :
    ne+ns+nm+nr ≤ (E+X)*V+T+R+k+5 := by
  nlinarith

/-- Full non-base node execution starting at its split block. No abstract
network or merge oracle is supplied: actual piece semantics yield the exact
physical merge input. Shared return restores the caller's headers and stacks. -/
theorem split_return (capacity : Fintype.card PC ≤ 2^k) (target : PC)
    (hw : v.width=125000*b) (hp : v.Positive) (hdiv : roleCount ∣ v.rows)
    (old hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime) (st : Tapes 2 prime)
    (hn : RecursiveStackAllocation.Available 0 node)
    (hd : RecursiveStackAllocation.Available 0 st) (hpc : RecursiveStackAllocation.Available 1 st)
    (x : Fin (volume prime v) → ZMod 2) (C : ℕ)
    (calls : ∀ rs : List Bool, RecursiveDimensionBank.Headers (role v roleCount)
        (RecursiveRowsNodeHeaders.headers hs rs) →
      Calls capacity (v := role v roleCount) hw (RecursiveRowsNodeHeaders.headers hs rs) f p
        (RecursiveViewFrame.savedStack hs node)
        (RecursiveChildCallSetup.savedStacks old st (FiniteReturnStack.address capacity (encoding target))) C) :
    ∃ steps ≤ ((74+RecursiveRowsNode.rowConstant roleCount+RecursiveRowsNodeRoleBank.constant roleCount)+(128+RecursiveRowsNode.rowConstant roleCount))*volume prime v+
        (Shared50PieceSchedule.pieces.map (overhead k)).sum*volume prime (role v roleCount)+
        Shared50Parameters.s*C+RecursiveChildCallReturn.cost old hs+k+5,
      Machine.run (Shared50RecursiveControl.program capacity width pcStack (implementation k)) steps
        (entryConfig capacity .split (dataBank hs f p node
          (RecursiveChildCallSetup.savedStacks old st (FiniteReturnStack.address capacity (encoding target)))
          (RecursiveRowsSerialization.sourceData wires (encoded x)))) =
        some (entryConfig capacity target (dataBank old f p node st
          (RecursiveRowsSerialization.sourceData wires
            (encoded (Shared50RecursiveNodeRows.transpose (one_dvd _) x))))) := by
  let code := FiniteReturnStack.address capacity (encoding target)
  let saved := RecursiveChildCallSetup.savedStacks old st code
  let nodeSaved := RecursiveViewFrame.savedStack hs node
  let before := dataBank hs f p node saved (RecursiveRowsSerialization.sourceData wires (encoded x))
  let splitData := RecursiveRowsSerialization.roleData wires (Equiv.refl _) hdiv (encoded x)
  let out := RecursiveRowsSerialization.sourceData wires (Shared50RecursiveNodeRows.transpose hdiv (encoded x))
  have hc : 0 < roleCount := by decide
  have hpRole := RecursiveRowsNodeLayout.role_positive roleCount v hc hp hdiv
  obtain ⟨rs,hrs,ne,hne,hre⟩ := entry_run capacity hp hdiv hs hv f p node saved (encoded x)
  let reduced := RecursiveRowsNodeHeaders.headers hs rs
  let middle := dataBank reduced f p nodeSaved saved splitData
  let network := Shared50NodePieceTransport.run (v := role v roleCount) hw
    (Shared50RecursiveChildPermutation.child (v := role v roleCount) hw) Shared50PieceSchedule.pieces splitData
  let merged := dataBank hs f p node saved out
  obtain ⟨ns,hns,hrsched⟩ := Shared50RecursivePieceExecution.binary_schedule_bound capacity
    (v := role v roleCount) hw (Shared50RecursiveChildPermutation.child hw) hpRole reduced hrs f p
    nodeSaved saved (Shared50RecursiveChildPermutation.child_spec (v := role v roleCount) hw) C (calls rs hrs) splitData
    (by
      change Shared50RecursiveBinaryInvariant.Ready (RecursiveRowsSerialization.roleData wires (Equiv.refl _) hdiv (encoded x))
      rw [Shared50RecursiveNodeBinary.splitData_encoded]
      exact Shared50RecursiveBinaryInvariant.of_encoded _)
  obtain ⟨nm,hnm,hrm⟩ := merge_run capacity hw hp hdiv hs reduced hv hrs f p node saved hn x
  let after := dataBank old f p node st out
  obtain ⟨nr,hnr,hrr⟩ := restore_return capacity target (RecursiveRoleSerialization.roles out)
    old hs f p node st hd hpc
  change Machine.run _ ne (entryConfig capacity .split before) = some (entryConfig capacity first middle) at hre
  change Machine.run _ ns (entryConfig capacity first middle) =
    some (entryConfig capacity .merge (dataBank reduced f p nodeSaved saved network)) at hrsched
  change Machine.run _ nm (entryConfig capacity .merge (dataBank reduced f p nodeSaved saved network)) =
    some (entryConfig capacity .restore merged) at hrm
  change Machine.run _ nr (entryConfig capacity .restore merged) = some (entryConfig capacity target after) at hrr
  have hout : out = RecursiveRowsSerialization.sourceData wires
      (encoded (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) := by
    dsimp only [out]
    rw [Shared50RecursiveChildPermutation.transpose_independent hc (by decide : 0 < 1) hdiv (one_dvd _)]
    rfl
  refine ⟨ne+ns+nm+nr,by simpa only [Nat.add_assoc] using assembly_bound hne hns hnm hnr,?_⟩
  rw [run_add,run_add,run_add,hre,Option.bind_some,hrsched,Option.bind_some,
    hrm,Option.bind_some,hrr]
  rw [show after = dataBank old f p node st out from rfl,hout]

theorem guard_assembly_bound {A R k ng nn : ℕ} (hg : ng ≤ 3)
    (hn : nn ≤ A+R+k+5) : ng+nn ≤ A+R+k+8 := by omega

/-- Starting at the actual width guard, execute the complete recursive node
and return to the physically decoded caller address on the exact final bank. -/
theorem guard_return (capacity : Fintype.card PC ≤ 2^k) (target : PC)
    (hw : v.width=125000*b) (hp : v.Positive) (hdiv : roleCount ∣ v.rows)
    (old hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime) (st : Tapes 2 prime)
    (hn : RecursiveStackAllocation.Available 0 node)
    (hd : RecursiveStackAllocation.Available 0 st) (hpc : RecursiveStackAllocation.Available 1 st)
    (x : Fin (volume prime v) → ZMod 2) (C : ℕ)
    (calls : ∀ rs : List Bool, RecursiveDimensionBank.Headers (role v roleCount)
        (RecursiveRowsNodeHeaders.headers hs rs) →
      Calls capacity (v := role v roleCount) hw (RecursiveRowsNodeHeaders.headers hs rs) f p
        (RecursiveViewFrame.savedStack hs node)
        (RecursiveChildCallSetup.savedStacks old st (FiniteReturnStack.address capacity (encoding target))) C) :
    ∃ steps ≤ ((74+RecursiveRowsNode.rowConstant roleCount+RecursiveRowsNodeRoleBank.constant roleCount)+(128+RecursiveRowsNode.rowConstant roleCount))*volume prime v+
        (Shared50PieceSchedule.pieces.map (overhead k)).sum*volume prime (role v roleCount)+
        Shared50Parameters.s*C+RecursiveChildCallReturn.cost old hs+k+8,
      Machine.run (Shared50RecursiveControl.program capacity width pcStack (implementation k)) steps
        (entryConfig capacity .guard (dataBank hs f p node
          (RecursiveChildCallSetup.savedStacks old st (FiniteReturnStack.address capacity (encoding target)))
          (RecursiveRowsSerialization.sourceData wires (encoded x)))) =
        some (entryConfig capacity target (dataBank old f p node st
          (RecursiveRowsSerialization.sourceData wires
            (encoded (Shared50RecursiveNodeRows.transpose (one_dvd _) x))))) := by
  let before := dataBank hs f p node
    (RecursiveChildCallSetup.savedStacks old st (FiniteReturnStack.address capacity (encoding target)))
    (RecursiveRowsSerialization.sourceData wires (encoded x))
  obtain ⟨ng,hng,hg⟩ := Shared50RecursiveExecution.guard_jump capacity width pcStack
    (implementation k) before (hs 3) rfl
    (BinaryDescriptorStackRoundtrip.descriptor_encoded (hs 3)).symm (hv.2 3)
  have hbranch : Shared50RecursiveExecution.branch (Counter.value (hs 3)) = PC.split := by
    unfold Shared50RecursiveExecution.branch
    have hh : Counter.value (hs 3) = v.width := hv.1 3
    have hne : Counter.value (hs 3) ≠ 1 := by omega
    rw [ite_eq_right hne]
  rw [hbranch] at hg
  change Machine.run _ ng (entryConfig capacity .guard before) = some (entryConfig capacity .split before) at hg
  obtain ⟨nn,hnn,hr⟩ := split_return capacity target hw hp hdiv old hs hv f p node st hn hd hpc x C calls
  refine ⟨ng+nn,guard_assembly_bound hng hnn,?_⟩
  rw [run_add,hg,Option.bind_some]
  exact hr

end
end IntegerMultBounds.Machine.Shared50RecursiveNodeExecution
