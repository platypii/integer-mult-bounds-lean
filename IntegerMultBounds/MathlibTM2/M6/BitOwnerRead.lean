module

public import IntegerMultBounds.MathlibTM2.M6.BitCopyLabel
public import IntegerMultBounds.MathlibTM2.M8.AtomBank
import IntegerMultBounds.Machine.RowPaddingConstructedAlphabet

/-! The same permanent owner word in the tape and stack representations. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host
open Shared50ModularControl (prime)

theorem encodedOwnerCell {N : ℕ} (word : Fin N → ZMod 2) (j : ℤ) :
    (RadixToBinary.binaryEncoding (q := prime)).encode
      (putWord (fun _ => blank) 0 ((List.ofFn word).map SparseRoleCircuit.encode) j) =
    putWord (fun _ => blank) 0 (List.ofFn fun i => SparseRoleCircuit.encode (a := prime) (word i)) j := by
  rw [List.map_ofFn]
  have mapped := congrFun (RowPaddingConstructedAlphabet.map_array_word (a := prime)
    (fun _ => blank) 0 (SparseRoleCircuit.encode ∘ word)) j
  have bits : RowPaddingConstructedAlphabet.mapArray (a := prime) (SparseRoleCircuit.encode ∘ word) =
      fun i => SparseRoleCircuit.encode (a := prime) (word i) := by
    funext i
    by_cases h : word i = 1 <;> simp [RowPaddingConstructedAlphabet.mapArray,RowPaddingConstructedAlphabet.encoding,
      CountedLoopReuseAlphabet.encoding,SparseRoleCircuit.encode,bitSymbol,h]
  rw [bits] at mapped
  exact mapped

theorem phaseOwner_reads {k N : ℕ} (data : Fin k → Fin N → ZMod 2) (S : Stacks k prime) :
    RepT (phaseOwners data) S.L S.R ↔
      ∀ t j, readAt blank (S.L t) (S.R t) j = M8.AtomBank.arrTape (SparseRoleCircuit.encode ∘ data t) j := by
  have cell (t : Fin k) (j : ℤ) :
      M8.AtomBank.arrTape (SparseRoleCircuit.encode ∘ data t) j = (phaseOwners data).tape t j := by
    simpa only [List.map_ofFn,M8.AtomBank.arrTape,phaseOwners] using encodedOwnerCell (data t) j
  constructor
  · intro h t j
    rw [cell]
    simpa only [phaseOwners,sub_zero] using (h t j).symm
  · intro h t j
    rw [← cell]
    simpa only [phaseOwners,sub_zero] using (h t j).symm

end IntegerMultBounds.MathlibTM2.M6.BitNode
