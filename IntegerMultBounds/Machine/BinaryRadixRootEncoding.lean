import IntegerMultBounds.Machine.BinaryRadixRangePrepareAlphabet
import IntegerMultBounds.Machine.ArbitraryWidthHighOriginalEncoding

/-! The binary range wrapper and recursive radix interchange have the same
literal payload and full-transpose endpoints despite their descriptor views. -/
namespace IntegerMultBounds.Machine.BinaryRadixRootEncoding
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (volume)
open ArbitraryWidthHighLayout (originalDescriptor)
open RecursiveInterchangeScaling (Address)
variable {P e G B : ℕ}

theorem volume_eq (P e G B : ℕ) :
    volume prime (originalDescriptor P e G B) = RadixRangePadding.volume P (prime^e) G B := by
  simp [volume,originalDescriptor,RadixRangePadding.volume]

def rootArray {α : Type*} (x : Fin (RadixRangePadding.volume P (prime^e) G B) → α) :
    Fin (volume prime (originalDescriptor P e G B)) → α := fun z => x (Fin.cast (volume_eq P e G B) z)

theorem index_eq (a : Address (originalDescriptor P e G B)) :
    Fin.cast (volume_eq P e G B) (RecursiveInterchangeScaling.index a) =
      RadixRangePadding.index a.beforeRows a.h a.middle a.d a.after := by
  apply Fin.ext
  simp only [Fin.val_cast]
  rw [RecursiveInterchangeScaling.index_val]
  change (((((a.beforeRows.val*1+a.row.val)*1+a.before.val)*prime^e+a.h.val)*G+
    a.middle.val)*prime^e+a.d.val)*B+a.after.val =
    a.after.val+B*(a.d.val+prime^e*(a.middle.val+G*(a.h.val+prime^e*a.beforeRows.val)))
  rw [show a.row.val = 0 from Fin.val_eq_zero a.row,
    show a.before.val = 0 from Fin.val_eq_zero a.before]
  ring

theorem transpose_root {α : Type*} (x : Fin (RadixRangePadding.volume P (prime^e) G B) → α) :
    Shared50RecursiveNodeRows.transpose (one_dvd _) (rootArray x) =
      rootArray (RadixRangePadding.transpose x) := by
  funext z
  obtain ⟨a,ha⟩ := ArbitraryWidthHighFoldSemantics.index_surjective
    (originalDescriptor P e G B) z
  rw [← ha]
  have ht := Shared50RecursiveNodeTranspose.transpose_all (by decide : 0 < 1)
    (one_dvd _) (rootArray x) (Shared50RecursiveNodeTranspose.swapAddress a)
  have hi : Shared50RecursiveNodeTranspose.swapAddress
      (Shared50RecursiveNodeTranspose.swapAddress a) = a := rfl
  rw [hi] at ht
  rw [ht]
  unfold rootArray
  rw [index_eq,index_eq]
  change x (RadixRangePadding.index a.beforeRows a.d a.middle a.h a.after) =
    RadixRangePadding.transpose x (RadixRangePadding.index a.beforeRows a.h a.middle a.d a.after)
  exact (RadixRangePadding.transpose_entry x
    (⟨a.beforeRows.val,a.beforeRows.isLt⟩ : Fin P)
    (⟨a.h.val,a.h.isLt⟩ : Fin (prime^e))
    (⟨a.middle.val,a.middle.isLt⟩ : Fin G)
    (⟨a.d.val,a.d.isLt⟩ : Fin (prime^e))
    (⟨a.after.val,a.after.isLt⟩ : Fin B)).symm

def bitValue (b : Bool) : ZMod 2 := if b then 1 else 0

theorem encode_bit (b : Bool) :
    ArbitraryWidthHighExchangeJoinEncoding.encoded (fun _ : Fin 1 => bitValue b) 0 =
      (bitSymbol b : Fin (prime+4)) := by cases b <;> rfl

/-- No runtime conversion or copy separates the padded binary data and
recursive I/O source. -/
theorem source_bits (x : Fin (RadixRangePadding.volume P (prime^e) G B) → Bool) :
    ArbitraryWidthHighExchangeShared.sourceWord (rootArray (fun z => bitValue (x z))) =
      BinaryRadixRangePrepareAlphabet.word (a := prime) (fun z => bitSymbol (x z)) := by
  rw [ArbitraryWidthHighExchangeJoinEncoding.sourceWord_eq]
  unfold RadixHighBlockJoinLoop.word BinaryRadixRangePrepareAlphabet.word
  have he : ArbitraryWidthHighExchangeJoinEncoding.encoded (rootArray (fun z => bitValue (x z))) =
      rootArray (fun z => (bitSymbol (x z) : Fin (prime+4))) := by
    funext z
    exact encode_bit _
  rw [he]
  congr 1
  exact List.ofFn_congr (volume_eq P e G B) _

/-- The zero fill in numerical padding remains the literal false bit. -/
theorem pad_bits {P N G B : ℕ} (M : ℕ)
    (x : Fin (RadixRangePadding.volume P N G B) → Bool) :
    RadixRangePadding.pad M (bitSymbol false : Fin (prime+4)) (fun z => bitSymbol (x z)) =
      fun z => bitSymbol (RadixRangePadding.pad M false x z) := by
  funext z
  unfold RadixRangePadding.pad RecursiveRowPadding.pad
  dsimp only
  split_ifs <;> rfl

theorem source_transpose_bits (x : Fin (RadixRangePadding.volume P (prime^e) G B) → Bool) :
    ArbitraryWidthHighExchangeShared.sourceWord
      (Shared50RecursiveNodeRows.transpose (one_dvd _) (rootArray (fun z => bitValue (x z)))) =
      BinaryRadixRangePrepareAlphabet.word (a := prime)
        (RadixRangePadding.transpose (fun z => bitSymbol (x z))) := by
  rw [transpose_root]
  change ArbitraryWidthHighExchangeShared.sourceWord
    (rootArray (fun z => bitValue (RadixRangePadding.transpose x z))) = _
  rw [source_bits]
  rfl

end
end IntegerMultBounds.Machine.BinaryRadixRootEncoding
