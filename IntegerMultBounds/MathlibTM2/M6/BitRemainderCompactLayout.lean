module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderHandoffRow

/-! Crop the staging row before transposing its active and inherited fields. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)
open FlatCoordinateSchedule (bits bits_value bits_canonical)

private theorem castWord {α : Type} {m n : ℕ} (h : m=n) (f : Fin n → α) :
    List.ofFn (fun z => f (Fin.cast h z)) = List.ofFn f := by subst n; rfl

/-- Remove the unused labels before moving the active field. This leaves a
compact A-by-B array of K-symbol records and restores both tape heads. -/
theorem singleLabelBank_crop_hoare {w B K : ℕ} (hB : 0 < B) (hK : 0 < K) :
    let A := (prime^w)^16
    let N := prime^(64*(w*64))
    ∀ (x : Fin 142081 → Fin (A*(B*K)) → ZMod 2) i,
    let input := List.ofFn (SparseRoleCircuit.encoded (a := prime) (singleLabelBank (firstRowLabel w) x) i)
    let output := List.ofFn (SparseRoleCircuit.encoded (a := prime) x i)
    HoareTime RowPaddingConstructedAlphabet.cropProgram
      (fun v => v = RowPaddingConstructedAlphabet.bank (putWord (fun _ => blank) 0 input) (fun _ => blank) 0 0
        (bits (A*B)) (bits 1) (bits N) (bits K))
      (fun v => v = RowPaddingConstructedAlphabet.bank
        (RowPaddingConstructedAlphabet.erased (putWord (fun _ => blank) 0 input) 0 (A*B*N*K))
        (putWord (fun _ => blank) 0 output) 0 0 (bits (A*B)) (bits 1) (bits N) (bits K))
      (413*(A*B)*(N*K)) := by
  intro A N x i input output
  have hs : A*B*1*K = A*(B*K) := by simp [Nat.mul_assoc]
  have hd : A*(B*N*K) = A*B*N*K := by simp [Nat.mul_assoc]
  let source := fun z => x i (Fin.cast hs z)
  let padded := RecursiveRowPadding.pad (A := A*B) (R := 1) (L := K) N 0 source
  have hN : 1 ≤ N := pow_pos Shared50ModularControl.prime_prime.pos _
  have run := RowPaddingConstructedAlphabet.crop_bits_hoare (a := prime) (fun _ => blank) (fun _ => blank)
    0 0 _ _ _ _ (A*B) 1 N K (fun z => decide (padded z = 1))
    (bits_value _) (bits_value _) (bits_value _) (bits_value _)
    (bits_canonical _) (bits_canonical _) (bits_canonical _) (bits_canonical _)
    (Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hB) Nat.zero_lt_one hN hK
  have src : input = List.ofFn (fun z => SparseRoleCircuit.encode (a := prime) (padded z)) := by
    rw [← castWord hd (fun z => SparseRoleCircuit.encode (a := prime) (padded z))]
    apply congrArg List.ofFn
    funext z
    exact congrArg SparseRoleCircuit.encode (singleLabelBank_pad x i z)
  have cropped := RecursiveRowPadding.crop_pad (A := A*B) (L := K) hN (0 : ZMod 2) source
  have dst : output = List.ofFn (RecursiveRowPadding.crop hN
      (fun z => SparseRoleCircuit.encode (a := prime) (padded z))) := by
    unfold output
    rw [← castWord hs (SparseRoleCircuit.encoded (a := prime) x i)]
    apply congrArg List.ofFn
    funext z
    exact congrArg SparseRoleCircuit.encode (congrFun cropped z).symm
  rw [src,dst]
  exact run

/-- The compact transpose puts each inherited block's active rows together.
Ordinary padding can then use the entire active-by-spectator field as one word. -/
def compactTranspose {A B K : ℕ} {α : Type} (x : Fin (A*(B*K)) → α) (j : Fin (B*(A*K))) : α :=
  let block := finProdFinEquiv.symm j
  let cell := finProdFinEquiv.symm block.2
  x (finProdFinEquiv (cell.1,finProdFinEquiv (block.1,cell.2)))

theorem compactTranspose_pad {A B K N : ℕ} {α : Type} (zero : α)
    (x : Fin (A*(B*K)) → α) (b : Fin B) (g : Fin N) (a : Fin A) (k : Fin K) :
    RecursiveRowPadding.pad (A := B) (R := 1) (L := A*K) N zero
      (fun j => compactTranspose x (j.cast (by simp)))
      (finProdFinEquiv (finProdFinEquiv (b,g),finProdFinEquiv (a,k))) =
      if g.val = 0 then x (finProdFinEquiv (a,finProdFinEquiv (b,k))) else zero := by
  simp only [RecursiveRowPadding.pad,Equiv.symm_apply_apply]
  split <;> rename_i h
  · rw [ite_eq_left (by omega)]
    have idx : (RecursiveInterchangeRows.pack (RecursiveInterchangeRows.pack b (⟨g.val,h⟩ : Fin 1))
        (finProdFinEquiv (a,k))).cast (show B*1*(A*K) = B*(A*K) by simp) =
        finProdFinEquiv (b,finProdFinEquiv (a,k)) := by
      apply Fin.ext
      simp [RecursiveInterchangeRows.pack,finProdFinEquiv_apply_val,show g.val = 0 by omega]
    rw [idx]
    simp [compactTranspose]
  · rw [ite_eq_right (by omega)]

/-- Ordinary padding treats the whole active field as one record, preserving the
compact transpose on the first label of every inherited block. -/
theorem compactTranspose_pad_hoare {A B K N : ℕ} (hB : 0 < B) (hW : 0 < A*K) (hN : 1 ≤ N)
    (x : Fin (A*(B*K)) → ZMod 2) :
    let compact := List.ofFn (fun j => SparseRoleCircuit.encode (a := prime) (compactTranspose x j))
    let padded := RecursiveRowPadding.pad (A := B) (R := 1) (L := A*K) N 0
      (fun j => compactTranspose x (j.cast (by simp)))
    let output := List.ofFn (fun j => SparseRoleCircuit.encode (a := prime) (padded j))
    HoareTime RowPaddingConstructedAlphabet.program
      (fun v => v = RowPaddingConstructedAlphabet.bank (putWord (fun _ => blank) 0 compact) (fun _ => blank)
        0 0 (bits B) (bits 1) (bits N) (bits (A*K)))
      (fun v => v = RowPaddingConstructedAlphabet.bank
        (RowPaddingConstructedAlphabet.erased (putWord (fun _ => blank) 0 compact) 0 (B*1*(A*K)))
        (putWord (fun _ => blank) 0 output) 0 0 (bits B) (bits 1) (bits N) (bits (A*K)))
      (413*B*(N*(A*K))) := by
  intro compact padded output
  let source := fun j : Fin (B*1*(A*K)) => compactTranspose x (j.cast (by simp))
  have run := RowPaddingConstructedAlphabet.pad_bits_hoare (a := prime) (fun _ => blank) (fun _ => blank)
    0 0 _ _ _ _ B 1 N (A*K) (fun z => decide (source z = 1)) (bits_value _) (bits_value _)
    (bits_value _) (bits_value _) (bits_canonical _) (bits_canonical _) (bits_canonical _) (bits_canonical _)
    hB Nat.zero_lt_one hN hW
  have src : compact = List.ofFn (fun z => SparseRoleCircuit.encode (a := prime) (source z)) :=
    (castWord (show B*1*(A*K) = B*(A*K) by simp) _).symm
  have dst : output = List.ofFn (RecursiveRowPadding.pad (A := B) (R := 1) (L := A*K) N
      (bitSymbol false) (fun z => SparseRoleCircuit.encode (a := prime) (source z))) := by
    apply congrArg List.ofFn
    funext z
    dsimp only [padded,RecursiveRowPadding.pad]
    split <;> rfl
  rw [src,dst]
  exact run

/-- Crop the restored first label back to the compact return-transpose input. -/
theorem compactTranspose_crop_hoare {A B K N : ℕ} (hB : 0 < B) (hW : 0 < A*K) (hN : 1 ≤ N)
    (x : Fin (A*(B*K)) → ZMod 2) :
    let compact := List.ofFn (fun j => SparseRoleCircuit.encode (a := prime) (compactTranspose x j))
    let padded := RecursiveRowPadding.pad (A := B) (R := 1) (L := A*K) N 0
      (fun j => compactTranspose x (j.cast (by simp)))
    let output := List.ofFn (fun j => SparseRoleCircuit.encode (a := prime) (padded j))
    HoareTime RowPaddingConstructedAlphabet.cropProgram
      (fun v => v = RowPaddingConstructedAlphabet.bank (putWord (fun _ => blank) 0 output) (fun _ => blank)
        0 0 (bits B) (bits 1) (bits N) (bits (A*K)))
      (fun v => v = RowPaddingConstructedAlphabet.bank
        (RowPaddingConstructedAlphabet.erased (putWord (fun _ => blank) 0 output) 0 (B*N*(A*K)))
        (putWord (fun _ => blank) 0 compact) 0 0 (bits B) (bits 1) (bits N) (bits (A*K)))
      (413*B*(N*(A*K))) := by
  intro compact padded output
  let source := fun j : Fin (B*1*(A*K)) => compactTranspose x (j.cast (by simp))
  have run := RowPaddingConstructedAlphabet.crop_bits_hoare (a := prime) (fun _ => blank) (fun _ => blank)
    0 0 _ _ _ _ B 1 N (A*K) (fun z => decide (padded z = 1)) (bits_value _) (bits_value _)
    (bits_value _) (bits_value _) (bits_canonical _) (bits_canonical _) (bits_canonical _) (bits_canonical _)
    hB Nat.zero_lt_one hN hW
  have inverse := RecursiveRowPadding.crop_pad (A := B) (L := A*K) hN (0 : ZMod 2) source
  have dst : compact = List.ofFn (RecursiveRowPadding.crop hN
      (fun z => SparseRoleCircuit.encode (a := prime) (padded z))) := by
    unfold compact
    rw [← castWord (show B*1*(A*K) = B*(A*K) by simp) _]
    apply congrArg List.ofFn
    funext z
    exact congrArg SparseRoleCircuit.encode (congrFun inverse z).symm
  rw [dst]
  exact run

/-- One complete compact scan per active row fits within the original
padded volume, even when the inherited block count is unrelated to the radix. -/
theorem compactTranspose_scan_bound (w B K : ℕ) :
    (prime^w)^16 * ((prime^w)^16*(B*K)) ≤ (prime^w)^16*(B*prime^(64*(w*64))*K) := by
  have radix := Shared50ModularControl.prime_prime.pos
  have width : (prime^w)^16 ≤ prime^(64*(w*64)) := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right radix (by omega)
  exact Nat.mul_le_mul_left _ (by
    calc
      (prime^w)^16*(B*K) = B*(prime^w)^16*K := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ width))

end IntegerMultBounds.MathlibTM2.M6.BitNode
