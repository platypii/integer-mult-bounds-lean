module

public import IntegerMultBounds.MathlibTM2.M8.Machine.InductionBaseWithin
public import IntegerMultBounds.MathlibTM2.M8.Machine.NodeExecution
public import IntegerMultBounds.MathlibTM2.M8.Machine.CallInductionBridge
public import IntegerMultBounds.MathlibTM2.M8.Machine.Budget

public import IntegerMultBounds.MathlibTM2.M8.Machine.CallExecutionWithin

/-! The bounded depth contract uses the same canonical input and restored output
as the existing execution induction. Literal calls reuse its bank adapters. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.InductionWithin
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Control
open Implementation (implementation widthSlot pcStack)
open BaseExecution (entryConfig)
open Shared50RecursiveBank (bank)
open CallReady (Ready)
open Shared50RecursiveNodeSemantics (encoded)
open Shared50RecursiveNodeRows (transpose)
open NodeLayout (wires)
open RecursiveRoleSerialization (roles)
open RecursiveInterchangeLayout (Descriptor volume role)
open SharedBankStageInput (raw)
variable {k : ℕ}

def Contract (capacity : Fintype.card PC ≤ 2^k) (depth D : ℕ) (lo hi : ℤ) : Prop :=
  ∀ (target : PC) (v : Descriptor) (_shape : Depth.Shape depth v)
    (hs old : Fin 6 → List Bool) (_hv : RecursiveDimensionBank.Headers v hs)
    (_hold : ∀ i, (old i).length ≤ 2*volume prime v)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (_ready : Ready f p node scalar st) (x : Fin (volume prime v) → ZMod 2),
    let initial := ((raw (bank (roles (RecursiveRowsSerialization.sourceData wires (encoded x))) hs f p node scalar
          (SharedBank.empty 0 prime) (RecursiveChildCallSetup.savedStacks old st
            (FiniteReturnStack.address capacity (encoding target))))
          (tapeCount capacity widthSlot pcStack (implementation k))).start
          (Control.program capacity widthSlot pcStack (implementation k)))
    (∀ j, lo+(D*volume prime v : ℕ) ≤ initial.tapes.head j ∧
      initial.tapes.head j+(D*volume prime v : ℕ) ≤ hi) →
    ∃ n ≤ Budget.budget k depth (volume prime v),
      RunWithin (Control.program capacity widthSlot pcStack (implementation k))
        (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) n initial
      (entryConfig capacity target
        (bank (roles (RecursiveRowsSerialization.sourceData wires (encoded (transpose (one_dvd v.rows) x))))
          old f p node scalar (SharedBank.empty 0 prime) st))

/-- The same coefficient covers depth zero once it covers the linear base budget. -/
theorem base (capacity : Fintype.card PC ≤ 2^k) (D : ℕ) (lo hi : ℤ)
    (hD : Budget.base k ≤ D) : Contract capacity 0 D lo hi := by
  intro target v shape hs old hv hold f p node scalar st ready x initial hmargin
  apply InductionBase.run_within capacity target v shape hs old hv hold f p node scalar st ready x lo hi
  intro j
  have hm := hmargin j
  have hb := Nat.mul_le_mul_right (volume prime v) hD
  change lo+(D*volume prime v : ℕ) ≤
    (raw (bank (roles (RecursiveRowsSerialization.sourceData wires (encoded x))) hs f p node scalar
      (SharedBank.empty 0 prime) (RecursiveChildCallSetup.savedStacks old st
        (FiniteReturnStack.address capacity (encoding target))))
      (tapeCount capacity widthSlot pcStack (implementation k))).head j ∧
    (raw (bank (roles (RecursiveRowsSerialization.sourceData wires (encoded x))) hs f p node scalar
      (SharedBank.empty 0 prime) (RecursiveChildCallSetup.savedStacks old st
        (FiniteReturnStack.address capacity (encoding target))))
      (tapeCount capacity widthSlot pcStack (implementation k))).head j+(D*volume prime v : ℕ) ≤ hi at hm
  dsimp only [Budget.budget]
  omega

theorem calls {depth b : ℕ} {v : Descriptor} (capacity : Fintype.card PC ≤ 2^k)
    (D : ℕ) (lo hi : ℤ) (ih : Contract capacity depth D lo hi) (hw : v.width=Machine.width*b) (hp : v.Positive)
    (childShape : ∀ i j : Fin Machine.width,
      Depth.Shape depth (RecursiveAffineViews.cross prime b v i j))
    (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Ready f p node (SharedBank.empty 1 prime) st) :
    ∀ (site : Site) w i j, pieces[site] = .call w i j →
    ∀ data : RecursiveViewedAction.Data payloadCount v, BinaryInvariant.Ready data →
    (∀ z, lo+(PieceExecution.callReserve D k w i j*volume prime v : ℕ) ≤
      (raw (PieceExecution.dataBank hs f p node st data)
        (tapeCount capacity widthSlot pcStack (implementation k))).head z ∧
      (raw (PieceExecution.dataBank hs f p node st data)
        (tapeCount capacity widthSlot pcStack (implementation k))).head z+
        (PieceExecution.callReserve D k w i j*volume prime v : ℕ) ≤ hi) →
    ∃ n ≤ PieceExecution.actualCallBound (v := v) k
        (Budget.budget k depth (volume prime v)) w i j,
      RunWithin (Control.program capacity widthSlot pcStack (implementation k))
        (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) n
        (entryConfig capacity (.piece site) (PieceExecution.dataBank hs f p node st data))
        (entryConfig capacity (successor site) (PieceExecution.dataBank hs f p node st
          (ChildPermutation.child hw w i j data))) := by
  intro site w i j hic data hdata hbank
  obtain ⟨bits,rfl⟩ := hdata
  let mid := CallReady.parkedBank w bits hs f p node
    (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) st
  have htrace : ∀ ch : Fin 6 → List Bool,
      RecursiveDimensionBank.Headers (RecursiveInterchangeLayout.child prime 1 b v i j) ch →
      (∀ z, lo+(D*volume prime v : ℕ) ≤
        (raw (RecursiveCallProtocol.childBank mid ch
          (node.append ((SharedBank.empty 1 prime).append (SharedBank.empty 0 prime)))
          (RecursiveChildCallSetup.savedStacks hs st (returnCode capacity site)))
          (tapeCount capacity widthSlot pcStack (implementation k))).head z ∧
        (raw (RecursiveCallProtocol.childBank mid ch
          (node.append ((SharedBank.empty 1 prime).append (SharedBank.empty 0 prime)))
          (RecursiveChildCallSetup.savedStacks hs st (returnCode capacity site)))
          (tapeCount capacity widthSlot pcStack (implementation k))).head z+(D*volume prime v : ℕ) ≤ hi) →
      ∃ n ≤ Budget.budget k depth (volume prime v),
        RunWithin (Control.program capacity widthSlot pcStack (implementation k))
          (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) n
          (entryConfig capacity .guard (RecursiveCallProtocol.childBank mid ch
            (node.append ((SharedBank.empty 1 prime).append (SharedBank.empty 0 prime)))
            (RecursiveChildCallSetup.savedStacks hs st (returnCode capacity site))))
        (entryConfig capacity (.recover site) (SharedPlacementAlphabet.setTape mid
          (RecursiveCallBank.role (u := 1+(1+0)) io).val
          (RecursiveShiftRoleBank.source (Shared50RecursiveChildPermutation.array hw i j (encoded (bits w)))) 0)) := by
    intro ch hch hmargin
    have hr := CallInductionBridge.ready_original w bits hs f p node
      (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) st ready
    have hold : ∀ z, (hs z).length ≤ 2*volume prime (RecursiveAffineViews.cross prime b v i j) := by
      rw [RecursiveAffineViews.cross_volume prime b v i j hw]
      exact RecursiveRowsNode.header_length v hp hs hv
    have hin := CallInductionBridge.input_bank w i j hw bits hs ch f p node
      (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) st
      (RecursiveChildCallSetup.savedStacks hs st (returnCode capacity site))
    have hm := hmargin
    dsimp only [mid,returnCode] at hin hm
    rw [hin, ← RecursiveAffineViews.cross_volume prime b v i j hw] at hm
    obtain ⟨n,hn,ht⟩ := ih (.recover site) (RecursiveAffineViews.cross prime b v i j)
      (childShape i j) ch hs hch hold (mid.tape (RecursiveCallBank.controlSlot 2))
      (mid.head (RecursiveCallBank.controlSlot 2)) node (SharedBank.empty 1 prime) st hr
      (Shared50RecursiveChildPermutation.toChild hw i j (bits w)) hm
    rw [RecursiveAffineViews.cross_volume prime b v i j hw] at hn
    have hout := CallInductionBridge.returned_bank w i j hw bits hs f p node
      (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) st
    change RunWithin _ _ n (entryConfig capacity .guard _) (entryConfig capacity (.recover site) _) at ht
    dsimp only [mid] at ht
    dsimp only at hout
    rw [← hin,hout] at ht
    exact ⟨n,hn,ht⟩
  have hcall := PieceExecution.call_actual_within (capacity := capacity) (hw := hw)
    (hp := hp) (hs := hs) (hv := hv) (f := f) (p := p) (node := node) (st := st)
    site w i j hic (encodedBits bits (fun _ => blank))
    (Shared50RecursiveChildPermutation.array hw i j (encoded (bits w))) (encodedBits_io _ _) ready.payload _ D lo hi hbank htrace
  have he : encodedBits bits (fun _ => blank) (wireSlot w) =
      encoded (bits w) := encodedBits_wire bits _ w
  simpa only [PieceExecution.actualCallBound,ChildPermutation.child,he] using hcall

end
end IntegerMultBounds.MathlibTM2.M8.Machine.InductionWithin
