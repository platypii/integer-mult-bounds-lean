module

public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeJoinEncoding
public import IntegerMultBounds.Machine.SparseRoleCircuit

/-! The cover routes and the pointwise COPY gates share the same owner tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)

noncomputable def copyOwners {T : ℕ} {v : Descriptor}
    (x : Fin T → Fin (volume prime v) → ZMod 2) : Tapes T prime :=
  ⟨fun _ => 0,fun k => sourceWord (x k)⟩

theorem sourceWord_cast {v : Descriptor} {N : ℕ} (size : volume prime v = N)
    (x : Fin N → ZMod 2) :
    sourceWord (fun i => x (Fin.cast size i)) =
      putWord (fun _ => blank) 0 (List.ofFn fun i => SparseRoleCircuit.encode (a := prime) (x i)) := by
  subst N
  rw [M8.Machine.ArbitraryWidthHighExchangeJoinEncoding.sourceWord_eq]
  unfold RadixHighBlockJoinLoop.word
  congr 2

/-- Only the two loop controls are appended when the routed owner bank is
viewed as the input to a pointwise gate. The volume cast preserves its bits. -/
theorem copyOwners_controls {T N : ℕ} {v : Descriptor} (size : volume prime v = N)
    (x : Fin T → Fin N → ZMod 2) (bs : List Bool) :
    PointwiseRoleGate.bank (a := prime) (fun _ _ => blank) (fun _ => 0) (SparseRoleCircuit.encoded x) bs =
      (copyOwners (v := v) (fun k i => x k (Fin.cast size i))).append
        (CountedLoopReuseAlphabet.controls CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary bs) 1 1) := by
  unfold PointwiseRoleGate.bank copyOwners
  congr 1
  apply congrArg₂ Tapes.mk rfl
  funext k
  exact (sourceWord_cast size (x k)).symm

end IntegerMultBounds.MathlibTM2.M6.BitNode
