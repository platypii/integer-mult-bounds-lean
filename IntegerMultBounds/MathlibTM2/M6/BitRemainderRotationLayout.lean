module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderRowRotation
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderCompactLayout

/-! Identify the serialized rotation tapes with the ordinary remainder bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _).ne'⟩

private theorem rangeMap (n : ℕ) {α : Type} (f : ℕ → α) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_get <;> simp

private theorem packWord {α : Type} {m n : ℕ} (f : Fin (m*n) → α) :
    List.ofFn f = (List.ofFn fun i : Fin m => List.ofFn fun j : Fin n => f (finProdFinEquiv (i,j))).flatten := by
  simpa only [finProdFinEquiv,Equiv.coe_fn_mk,Nat.add_comm,Nat.mul_comm] using List.ofFn_mul f

/-- A block address outside the stream is never read. Its default still has the
width required by the streaming machine. -/
def rotationRecord {B W : ℕ} (x : Fin B → Fin W → ZMod 2) (b : ℕ) : List (Fin 4) :=
  List.ofFn (fun k : Fin W => SparseRoleCircuit.encode (a := 0) (if h : b < B then x ⟨b,h⟩ k else 0))

theorem rotationRecord_length {B W : ℕ} (x : Fin B → Fin W → ZMod 2) (b : ℕ) :
    (rotationRecord x b).length = W := List.length_ofFn

/-- Equality of complete tape words, including the zero symbols on inactive labels. -/
theorem rotationStream_word {B N W : ℕ} (g : Fin N) (x : Fin B → Fin W → ZMod 2)
    (f : Fin ((B*N)*W) → ZMod 2)
    (cell : ∀ b j k, f (finProdFinEquiv (finProdFinEquiv (b,j),k)) = if j = g then x b k else 0) :
    (TranslationStream.fibers N B (fun b j => if j = g.val then rotationRecord x b
      else List.replicate W (SparseRoleCircuit.encode (a := 0) 0))).flatten.map
      (CountedLoopReuseAlphabet.encoding prime).encode = List.ofFn (fun i => SparseRoleCircuit.encode (a := prime) (f i)) := by
  rw [packWord (fun i => SparseRoleCircuit.encode (a := prime) (f i))]
  rw [packWord (fun i : Fin (B*N) => List.ofFn fun k : Fin W => SparseRoleCircuit.encode (a := prime) (f (finProdFinEquiv (i,k))))]
  simp only [TranslationStream.fibers,TranslationStream.blocks,rangeMap,List.map_flatten,List.map_ofFn,
    List.flatten_flatten,Function.comp_def]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext b
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext j
  by_cases h : j = g
  · subst j
    simp [rotationRecord,b.isLt,cell,Function.comp_def]
    rfl
  · have ne : j.val ≠ g.val := fun e => h (Fin.ext e)
    simp [ne,cell,h]
    exact Or.inr rfl

/-- In physical block order, rotation starts from the output of ordinary padding. -/
theorem paddedRotation_word {A B N K : ℕ} [NeZero N] (x : Fin (A*(B*K)) → ZMod 2) :
    let row := fun b k => compactTranspose x (finProdFinEquiv (b,k))
    let padded := RecursiveRowPadding.pad (A := B) (R := 1) (L := A*K) N 0
      (fun j => compactTranspose x (j.cast (by simp)))
    (TranslationStream.fibers N B (fun b j => if j = 0 then rotationRecord row b
      else List.replicate (A*K) (SparseRoleCircuit.encode (a := 0) 0))).flatten.map
      (CountedLoopReuseAlphabet.encoding prime).encode =
      List.ofFn (fun i => SparseRoleCircuit.encode (a := prime) (padded i)) := by
  intro row padded
  apply rotationStream_word (0 : Fin N) row padded
  intro b j k
  obtain ⟨⟨a,k⟩,rfl⟩ := finProdFinEquiv.surjective k
  simpa only [padded,row,compactTranspose,Equiv.symm_apply_apply,Fin.ext_iff,Fin.val_zero] using compactTranspose_pad (N := N) 0 x b j a k

/-- Rotating to the identity label produces exactly the ordinary owner word. -/
theorem identityRotation_word {w B K : ℕ}
    (x : Fin 142081 → Fin ((prime^w)^16*(B*K)) → ZMod 2) (i : Fin 142081) :
    let A := (prime^w)^16
    let N := prime^(64*(w*64))
    let g := ordinaryIdentityRow w
    let row := fun b k => compactTranspose (x i) (finProdFinEquiv (b,k))
    let bank := fun j => singleLabelBank (firstRowLabel w) x i ((ordinaryRowLayout (Equiv.swap 0 g)).symm j)
    (TranslationStream.fibers N B (fun b j => if j = g.val then rotationRecord row b
      else List.replicate (A*K) (SparseRoleCircuit.encode (a := 0) 0))).flatten.map
      (CountedLoopReuseAlphabet.encoding prime).encode =
      List.ofFn (fun j => SparseRoleCircuit.encode (a := prime) (bank j)) := by
  intro A N g row bank
  apply rotationStream_word g row bank
  intro b j k
  obtain ⟨⟨a,k⟩,rfl⟩ := finProdFinEquiv.surjective k
  simpa only [bank,g,row,compactTranspose,Equiv.symm_apply_apply] using ordinaryIdentityRow_payload x i a b j k

end IntegerMultBounds.MathlibTM2.M6.BitNode
