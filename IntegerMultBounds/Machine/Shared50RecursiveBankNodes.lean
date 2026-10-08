import IntegerMultBounds.Machine.Shared50RecursiveBank

/-! Concrete node blocks on the same permanent bank as recursive calls. The
node frame and the blank scalar-view frame occupy different physical tapes. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveBankNodes
noncomputable section
open Networks
open Shared50ModularControl (prime)
open SharedBankStageInput (raw)
open Shared50RecursiveBank
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveViewedAction (Data)
open RecursiveRoleSerialization (roles)
variable {t u c b : ℕ} {v : Descriptor}

def entry (wires : Fin (1+c) → Fin t) (hw : Function.Injective wires) :=
  adapt (RecursiveRowsNode.entry (u := AuxCount u-1) wires hw) (commonRename nodeSlot)
def exit (rho : Equiv.Perm (Fin c)) (wires : Fin (1+c) → Fin t) (hw : Function.Injective wires) :=
  adapt (RecursiveRowsNode.exit (u := AuxCount u-1) rho wires hw) (commonRename nodeSlot)
def segment (seg : Shared50OrderedPieces.Segment) :=
  adapt (Shared50NodeSegments.machine (u := AuxCount u-1) seg) (commonRename scalarSlot)
def gate (g : Shared50OrderedPieces.Gate) :=
  adapt (Shared50NodeGates.machine (u := AuxCount u-1) g) (commonRename nodeSlot)

theorem entry_hoare (wires : Fin (1+c) → Fin t) (hw : Function.Injective wires)
    (hs : Fin 6 → List Bool) (node scalar : Tapes 1 prime)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (aux : Tapes u prime) (st : Tapes 2 prime)
    (v : Descriptor) (hc : 0 < c) (hv : RecursiveDimensionBank.Headers v hs)
    (hp : v.Positive) (hd : c ∣ v.rows) (x : Fin (volume prime v) → Fin 4) :
    ∃ rs : List Bool, RecursiveDimensionBank.Headers (RecursiveInterchangeLayout.role v c)
      (RecursiveRowsNodeHeaders.headers hs rs) ∧
      HoareTime (entry (u := u) wires hw).program
        (fun w => w = raw (bank (roles (RecursiveRowsSerialization.sourceData wires x))
          hs f p node scalar aux st) (entry (u := u) wires hw).tapes)
        (fun w => w = raw (bank (roles (RecursiveRowsSerialization.roleData wires (Equiv.refl _) hd x))
          (RecursiveRowsNodeHeaders.headers hs rs) f p (RecursiveViewFrame.savedStack hs node) scalar aux st)
          (entry (u := u) wires hw).tapes)
        (RecursiveViewFrame.pushCost hs+RecursiveRowsClean.bound c (volume prime v)+
          RecursiveRowsNodeRoleBank.constant c*volume prime v+2) := by
  obtain ⟨rs,hh,h⟩ := RecursiveRowsNode.entry_hoare wires hw hs node
    (rest nodeSlot (auxiliary f p node scalar aux st)) v hc hv hp hd x
  have h' := adapt_realizes _ (commonRename nodeSlot) _ _ _ h
  rw [node_endpoint] at h'
  rw [rest_node f p node (RecursiveViewFrame.savedStack hs node) scalar aux st,node_endpoint] at h'
  exact ⟨rs,hh,h'⟩

theorem exit_hoare (rho : Equiv.Perm (Fin c)) (wires : Fin (1+c) → Fin t)
    (hw : Function.Injective wires) (old hs : Fin 6 → List Bool)
    (node scalar : Tapes 1 prime) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (aux : Tapes u prime) (st : Tapes 2 prime) (hf : RecursiveViewFrame.Free old node)
    (v : Descriptor) (hc : 0 < c) (hv : RecursiveDimensionBank.Headers v old)
    (hp : v.Positive) (hd : c ∣ v.rows) (x : Fin (volume prime v) → Fin 4) :
    HoareTime (exit (u := u) rho wires hw).program
      (fun w => w = raw (bank (roles (RecursiveRowsSerialization.roleData wires rho hd x))
        hs f p (RecursiveViewFrame.savedStack old node) scalar aux st) (exit (u := u) rho wires hw).tapes)
      (fun w => w = raw (bank (roles (RecursiveRowsSerialization.sourceData wires x))
        old f p node scalar aux st) (exit (u := u) rho wires hw).tapes)
      (RecursiveViewFrame.restoreCost old hs+RecursiveRowsClean.bound c (volume prime v)+1) := by
  have h := RecursiveRowsNode.exit_hoare rho wires hw old hs node
    (rest nodeSlot (auxiliary f p node scalar aux st)) hf v hc hv hp hd x
  have h' := adapt_realizes _ (commonRename nodeSlot) _ _ _ h
  rw [node_endpoint] at h'
  rw [rest_node f p node (RecursiveViewFrame.savedStack old node) scalar aux st,node_endpoint] at h'
  exact h'

theorem segment_hoare (seg : Shared50OrderedPieces.Segment) (hw : v.width=125000*b)
    (hp : v.Positive) (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime)
    (aux : Tapes u prime) (st : Tapes 2 prime) (data : Data Shared50NodeSegments.payloadCount v) :
    HoareTime (segment (u := u) seg).program
      (fun w => w = raw (bank (roles data) hs f p node (SharedBank.empty 1 prime) aux st) (segment (u := u) seg).tapes)
      (fun w => w = raw (bank (roles (Shared50NodeSegments.array seg hw data)) hs f p node
        (SharedBank.empty 1 prime) aux st) (segment (u := u) seg).tapes)
      (Shared50NodeSegments.coefficient seg*volume prime v) := by
  have h := Shared50NodeSegments.realizes seg hw hp hs hv
    (rest scalarSlot (auxiliary f p node (SharedBank.empty 1 prime) aux st)) data
  have h' := adapt_realizes _ (commonRename scalarSlot) _ _ _ h
  simp only [scalar_endpoint] at h'
  exact h'

theorem gate_hoare (g : Shared50OrderedPieces.Gate) (hp : v.Positive)
    (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (aux : Tapes u prime) (st : Tapes 2 prime) (data : Data Shared50NodeSegments.payloadCount v) :
    HoareTime (gate (u := u) g).program
      (fun w => w = raw (bank (roles data) hs f p node scalar aux st) (gate (u := u) g).tapes)
      (fun w => w = raw (bank (roles (Shared50NodeGates.array g data)) hs f p node scalar aux st) (gate (u := u) g).tapes)
      (51858*volume prime v) := by
  have h := Shared50NodeGates.realizes_array g hp hs hv node
    (rest nodeSlot (auxiliary f p node scalar aux st)) data
  have h' := adapt_realizes _ (commonRename nodeSlot) _ _ _ h
  simp only [node_endpoint] at h'
  exact h'

end
end IntegerMultBounds.Machine.Shared50RecursiveBankNodes
