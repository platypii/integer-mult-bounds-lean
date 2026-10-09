import IntegerMultBounds.Machine.ArbitraryWidthPaddedPieceArrays

/-! Actual row padding and reversed crop with descriptor-level binary endpoints. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthPaddedPiecePadding
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveInterchangeRows (rowLength)
open RecursiveRowPadding
open ArbitraryWidthPaddedPieceArrays (word)
open ArbitraryWidthHighExchangeShared (sourceWord)

def values (v : Descriptor) (R' : ℕ) : Fin 4 → ℕ :=
  ![v.beforeRows,v.rows,R',rowLength prime v]
def Headers (v : Descriptor) (R' : ℕ) (hs : Fin 4 → List Bool) : Prop :=
  (∀ i, Counter.value (hs i) = values v R' i) ∧ (∀ i, GrowingCounterData.Canonical (hs i))

def bank (source dest : ℤ → Fin (prime+4)) (hs : Fin 4 → List Bool) :=
  RowPaddingConstructedAlphabet.bank source dest 0 0 (hs 0) (hs 1) (hs 2) (hs 3)

def input {v : Descriptor} (x : Fin (volume prime v) → ZMod 2) (hs : Fin 4 → List Bool) :=
  bank (sourceWord x) (fun _ => blank) hs

def middle {v : Descriptor} (x : Fin (volume prime v) → ZMod 2) (hs : Fin 4 → List Bool) :=
  bank (fun _ => blank) (sourceWord x) hs

theorem rowLength_pos (v : Descriptor) (hp : v.Positive) : 0 < rowLength prime v := by
  unfold rowLength
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hp.2.2.1
    (pow_pos Shared50ModularControl.prime_prime.pos _)) hp.2.2.2.1)
    (pow_pos Shared50ModularControl.prime_prime.pos _)) hp.2.2.2.2

theorem pad_hoare (v : Descriptor) (R' : ℕ) (hs : Fin 4 → List Bool)
    (hp : v.Positive) (hR : v.rows ≤ R') (hv : Headers v R' hs)
    (x : Fin (volume prime v) → ZMod 2) :
    HoareTime (RowPaddingConstructedAlphabet.program (a := prime))
      (fun z => z = input x hs) (fun z => z = middle (padArray R' 0 x) hs)
      (413*volume prime (withRows v R')) := by
  have h := RowPaddingConstructedAlphabet.pad_bits_hoare (a := prime)
    (fun _ => blank) (fun _ => blank) 0 0 (hs 0) (hs 1) (hs 2) (hs 3)
    v.beforeRows v.rows R' (rowLength prime v) (fun z => decide (rowView x z = 1))
    (hv.1 0) (hv.1 1) (hv.1 2) (hv.1 3)
    (hv.2 0) (hv.2 1) (hv.2 2) (hv.2 3) hp.1 hp.2.1 hR (rowLength_pos v hp)
  change HoareTime _
    (fun z => z = bank (word (rowView x)) (fun _ => blank) hs)
    (fun z => z = bank (RowPaddingConstructedAlphabet.erased (word (rowView x)) 0 _)
      (putWord (fun _ => blank) 0 (List.ofFn (pad R' (bitSymbol false)
        (fun z => SparseRoleCircuit.encode (a := prime) (rowView x z))))) hs) _ at h
  rw [ArbitraryWidthPaddedPieceArrays.erased_word,ArbitraryWidthPaddedPieceArrays.encode_pad] at h
  change HoareTime _ (fun z => z = bank (word (rowView x)) (fun _ => blank) hs)
    (fun z => z = bank (fun _ => blank) (word (pad R' 0 (rowView x))) hs) _ at h
  have hinput : word (rowView x) = sourceWord x :=
    (ArbitraryWidthPaddedPieceArrays.word_rowView x).trans (ArbitraryWidthPaddedPieceArrays.word_source x)
  have hout : word (pad R' 0 (rowView x)) = sourceWord (padArray R' 0 x) := by
    calc
      _ = word (rowView (padArray R' 0 x)) := congrArg word (rowView_padArray R' 0 x).symm
      _ = word (padArray R' 0 x) := ArbitraryWidthPaddedPieceArrays.word_rowView _
      _ = _ := ArbitraryWidthPaddedPieceArrays.word_source _
  rw [hinput,hout] at h
  convert h using 1 <;> try rfl
  rw [volume_rows]
  change 413*(v.beforeRows*R'*rowLength prime v) = _
  ring

def swap : Fin 12 ≃ Fin 12 := Equiv.swap 0 1

theorem bank_swap (source dest : ℤ → Fin (prime+4)) (hs : Fin 4 → List Bool) :
    (bank source dest hs).reindex swap = bank dest source hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def cropProgram := Machine.reindex (RowPaddingConstructedAlphabet.cropProgram (a := prime)) swap

theorem crop_hoare (v : Descriptor) (R' : ℕ) (hs : Fin 4 → List Bool)
    (hp : v.Positive) (hR : v.rows ≤ R') (hv : Headers v R' hs)
    (x : Fin (volume prime (withRows v R')) → ZMod 2) :
    HoareTime cropProgram (fun z => z = middle x hs)
      (fun z => z = input (cropArray hR x) hs) (413*volume prime (withRows v R')) := by
  have h := RowPaddingConstructedAlphabet.crop_bits_hoare (a := prime)
    (fun _ => blank) (fun _ => blank) 0 0 (hs 0) (hs 1) (hs 2) (hs 3)
    v.beforeRows v.rows R' (rowLength prime v) (fun z => decide (rowView x z = 1))
    (hv.1 0) (hv.1 1) (hv.1 2) (hv.1 3)
    (hv.2 0) (hv.2 1) (hv.2 2) (hv.2 3) hp.1 hp.2.1 hR (rowLength_pos v hp)
  change HoareTime _
    (fun z => z = bank (word (rowView x)) (fun _ => blank) hs)
    (fun z => z = bank (RowPaddingConstructedAlphabet.erased (word (rowView x)) 0 _)
      (putWord (fun _ => blank) 0 (List.ofFn (crop hR
        (fun z => SparseRoleCircuit.encode (a := prime) (rowView x z))))) hs) _ at h
  have he : RowPaddingConstructedAlphabet.erased (word (rowView x)) 0
      (v.beforeRows*R'*rowLength prime v) = (fun _ => blank) :=
    ArbitraryWidthPaddedPieceArrays.erased_word (rowView x)
  rw [he] at h
  change HoareTime _ (fun z => z = bank (word (rowView x)) (fun _ => blank) hs)
    (fun z => z = bank (fun _ => blank) (word (crop hR (rowView x))) hs) _ at h
  have hinput : word (rowView x) = sourceWord x :=
    (ArbitraryWidthPaddedPieceArrays.word_rowView x).trans (ArbitraryWidthPaddedPieceArrays.word_source x)
  have hout : word (crop hR (rowView x)) = sourceWord (cropArray hR x) := by
    calc
      _ = word (rowView (cropArray hR x)) := congrArg word (rowView_cropArray hR x).symm
      _ = word (cropArray hR x) := ArbitraryWidthPaddedPieceArrays.word_rowView _
      _ = _ := ArbitraryWidthPaddedPieceArrays.word_source _
  rw [hinput,hout] at h
  have hh := hoare_reindex_eq h swap
  simp only [bank_swap] at hh
  convert hh using 1 <;> try rfl
  rw [volume_rows]
  change 413*(v.beforeRows*R'*rowLength prime v) = _
  ring

theorem middle_source {v w : Descriptor} (x : Fin (volume prime v) → ZMod 2)
    (y : Fin (volume prime w) → ZMod 2) (hs : Fin 4 → List Bool) :
    SharedPlacementAlphabet.setTape (middle x hs) 1 (sourceWord y) 0 = middle y hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.ArbitraryWidthPaddedPiecePadding
