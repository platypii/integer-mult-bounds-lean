import IntegerMultBounds.Machine.BinaryAddressOffsetHeaders
import IntegerMultBounds.Machine.CountedPackedShapeHeaders
import IntegerMultBounds.Compact.PowerTwoDigits
import IntegerMultBounds.Machine.BlockRotationData

/-! Literal parity-load offsets in increasing regular address order. Each
q-bit source digit contributes its low bit to the corresponding b-bit output
digit; this is the second modular line of the early-source gadget. -/
namespace IntegerMultBounds.Machine.BinaryAddressOffsetData
open BinaryAddressTableData

def source (q n : ℕ) := table (n*q) (2^(n*q))
def dummy (q n : ℕ) := List.replicate (n*2^(n*q)) false
def digit (b : ℕ) (x : Bool) := x :: List.replicate (b-1) false

def word (q b n : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :=
  Gather.gather (fun x _ => x) (PackedArith.parity q b hb hbq) (source q n) (dummy q n) (n*2^(n*q))

@[simp] theorem source_length (q n : ℕ) : (source q n).length=(n*2^(n*q))*q := by
  rw [source,table_length]; ring
@[simp] theorem dummy_length (q n : ℕ) : (dummy q n).length=n*2^(n*q) := List.length_replicate
@[simp] theorem digit_length (b : ℕ) (hb : 1 ≤ b) (x : Bool) : (digit b x).length=b := by
  simp [digit]; omega
@[simp] theorem word_length (q b n : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :
    (word q b n hb hbq).length=(n*2^(n*q))*b := by
  exact Gather.gather_length _ _ _ _ _

theorem table_entry (w N i j : ℕ) (hi : i<N) (hj : j<w) :
    (table w N).getD (i*w+j) false=(row w i).getD j false := by
  have hh := BlockRotationData.flatten_index w ((List.range N).map (row w))
    (by intro xs hx; obtain ⟨k,_,rfl⟩ := List.mem_map.mp hx; exact row_length w k)
    i j (by simpa using hi) hj
  simp only [List.getElem_map,List.getElem_range] at hh
  simp only [table,List.getD_eq_getElem?_getD,hh]

theorem source_entry (q n i j : ℕ) (hi : i<2^(n*q)) (hj : j<n) (hq : 0<q) :
    (source q n).getD ((i*n+j)*q) false=(row (n*q) i).getD (j*q) false := by
  have h := table_entry (n*q) (2^(n*q)) i (j*q) hi (Nat.mul_lt_mul_of_pos_right hj hq)
  simpa only [source,Nat.add_mul,Nat.mul_assoc] using h

theorem gather_digit (q b n k : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :
    Gather.digitWord (fun x _ => x) (PackedArith.parity q b hb hbq) (source q n) (dummy q n) k =
      digit b ((source q n).getD (k*q) false) := by
  simp [Gather.digitWord,PackedArith.parity,Gather.field,digit]

theorem word_flatten (q b n : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :
    word q b n hb hbq=
      ((List.range (n*2^(n*q))).map (fun k => digit b ((source q n).getD (k*q) false))).flatten := by
  rw [word,Compact.PowerTwo.gather_flatten]
  congr 2

/-- Literal low-bit destinations for every source address and packed digit. -/
theorem word_entry (q b n i j : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q)
    (hi : i<2^(n*q)) (hj : j<n) :
    (word q b n hb hbq).getD ((i*n+j)*b) false=(row (n*q) i).getD (j*q) false := by
  have hk : i*n+j<n*2^(n*q) := by nlinarith
  have hh := BlockRotationData.flatten_index b
    ((List.range (n*2^(n*q))).map (fun k => digit b ((source q n).getD (k*q) false)))
    (by intro xs hx; obtain ⟨k,_,rfl⟩ := List.mem_map.mp hx; exact digit_length b hb _)
    (i*n+j) 0 (by simpa using hk) (by omega)
  simp only [List.getElem_map,List.getElem_range,Nat.add_zero,digit,List.getElem?_cons_zero] at hh
  rw [word_flatten,List.getD_eq_getElem?_getD]
  simp only [digit]
  rw [hh,Option.getD_some]
  exact source_entry q n i j hi hj (by omega)

/-- Higher bits of each output digit are literal zeros, not unspecified padding. -/
theorem word_padding (q b n k r : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q)
    (hk : k<n*2^(n*q)) (hr : 0<r) (hrb : r<b) :
    (word q b n hb hbq).getD (k*b+r) false=false := by
  have hh := BlockRotationData.flatten_index b
    ((List.range (n*2^(n*q))).map (fun k => digit b ((source q n).getD (k*q) false)))
    (by intro xs hx; obtain ⟨k,_,rfl⟩ := List.mem_map.mp hx; exact digit_length b hb _)
    k r (by simpa using hk) hrb
  rw [word_flatten,List.getD_eq_getElem?_getD,hh]
  simp only [List.getElem_map,List.getElem_range,digit]
  have he : r=(r-1)+1 := by omega
  rw [he,List.getElem?_cons_succ]
  rw [List.getElem?_eq_getElem (by simp; omega)]
  simp

end IntegerMultBounds.Machine.BinaryAddressOffsetData
