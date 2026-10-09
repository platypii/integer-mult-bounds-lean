import IntegerMultBounds.Machine.BinaryParityXorOffsetData
import IntegerMultBounds.Compact.PackedArithValue

/-! The positive fourth-line gather packs parity XOR original controls
for each regular source address, before per-row modular negation. -/
namespace IntegerMultBounds.Machine.BinaryParityXorOffsetPositive
open BinaryParityXorOffsetData BinaryAddressTableData
open BinaryAddressOffsetRepeatData (copies)

private theorem copies_replicate (Z : List Bool) (N : ℕ) : copies Z N=(List.replicate N Z).flatten := by
  induction N with
  | zero => rfl
  | succ N ih => simp [BinaryAddressOffsetRepeatData.copies_succ,List.replicate_add,ih]

theorem controls_entry (q n i j : ℕ) (Z : List Bool) (hZ : Z.length=n)
    (hi : i<2^(n*q)) (hj : j<n) :
    (controls q n Z).getD (i*n+j) false=Z.getD j false := by
  have h := BlockRotationData.flatten_index n (List.replicate (2^(n*q)) Z)
    (by intro xs hx; obtain ⟨_,rfl⟩ := List.mem_replicate.mp hx; exact hZ)
    i j (by simpa using hi) hj
  rw [controls,BinarySelectedOffsetData.controls,copies_replicate,List.getD_eq_getElem?_getD,h]
  simp only [List.getElem_replicate,List.getD_eq_getElem?_getD]

private theorem source_field (q n i j : ℕ) (_hq : 0<q) (hi : i<2^(n*q)) (hj : j<n) :
    Gather.field (source q n) ((i*n+j)*q) 1=Gather.field (row (n*q) i) (j*q) 1 := by
  unfold Gather.field
  apply List.map_congr_left
  intro r hr
  have hrlt := List.mem_range.mp hr
  have h := BinaryAddressOffsetData.table_entry (n*q) (2^(n*q)) i (j*q+r) hi (by nlinarith)
  change (BinaryAddressOffsetData.source q n).getD ((i*n+j)*q+r) false=_
  simpa only [BinaryAddressOffsetData.source,Nat.add_mul,Nat.mul_assoc,Nat.add_assoc] using h

private theorem digit_eq (q b n i j : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q)
    (hZ : Z.length=n) (hi : i<2^(n*q)) (hj : j<n) :
    Gather.digitWord (fun x z => xor x z) (PackedArith.parity q b hb hbq)
      (source q n) (controls q n Z) (i*n+j)=
    Gather.digitWord (fun x z => xor x z) (PackedArith.parity q b hb hbq)
      (row (n*q) i) Z j := by
  simp only [Gather.digitWord,PackedArith.parity,Nat.add_zero]
  rw [source_field q n i j (by omega) hi hj,controls_entry q n i j Z hZ hi hj]

private theorem gather_bit (S : Gather.Shape) (X Z : List Bool) (N k r : ℕ)
    (hk : k<N) (hr : r<S.st) :
    (Gather.gather (fun x z => xor x z) S X Z N).getD (k*S.st+r) false=
      (Gather.digitWord (fun x z => xor x z) S X Z k).getD r false := by
  have h := BlockRotationData.flatten_index S.st
    ((List.range N).map (Gather.digitWord (fun x z => xor x z) S X Z))
    (by intro xs hx; obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx; exact Gather.digitWord_length _ _ _ _ _)
    k r (by simpa using hk) hr
  rw [Compact.PowerTwo.gather_flatten,List.getD_eq_getElem?_getD,h]
  simp only [List.getElem_map,List.getElem_range,List.getD_eq_getElem?_getD]

/-- Each generated row uses exactly the original control word, independently
of the regular temporary address; no repeated-control input is assumed. -/
theorem field_eq (q b n i : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q)
    (hZ : Z.length=n) (hi : i<2^(n*q)) :
    Gather.field (positiveWord q b n Z hb hbq) (i*(n*b)) (n*b)=rowWord q b n i Z hb hbq := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    have hjn : j<n*b := by simpa only [Gather.field_length] using hj
    have hk : j/b<n := (Nat.div_lt_iff_lt_mul (by omega)).mpr hjn
    have hr : j%b<b := Nat.mod_lt _ (by omega)
    have hbig : i*n+j/b<n*2^(n*q) := by nlinarith
    have hsplit : (j/b)*b+j%b=j := by simpa only [Nat.mul_comm] using Nat.div_add_mod j b
    have hindex : i*(n*b)+j=(i*n+j/b)*b+j%b := by nlinarith
    have hl := gather_bit (PackedArith.parity q b hb hbq) (source q n) (controls q n Z)
      (n*2^(n*q)) (i*n+j/b) (j%b) hbig hr
    have hh := gather_bit (PackedArith.parity q b hb hbq) (row (n*q) i) Z n (j/b) (j%b) hk hr
    rw [digit_eq q b n i (j/b) Z hb hbq hZ hi hk] at hl
    dsimp only [PackedArith.parity] at hl hh
    rw [hsplit] at hh
    rw [←hindex] at hl
    change (positiveWord q b n Z hb hbq).getD (i*(n*b)+j) false=_ at hl
    change (rowWord q b n i Z hb hbq).getD j false=_ at hh
    simp only [Gather.field,List.getElem_map,List.getElem_range]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj',Option.getD_some] at hh
    exact hl.trans hh.symm

theorem field_value (q b n i : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q)
    (hZ : Z.length=n) (hi : i<2^(n*q)) :
    (Counter.value (Gather.field (positiveWord q b n Z hb hbq) (i*(n*b)) (n*b)) : ℤ)=
      Compact.Radix.pack ((2 : ℤ)^b) (List.zipWith (fun v z => (v%2+z)%2)
        (Compact.Radix.digits ((2 : ℤ)^q) n i) (Z.map Compact.PowerTwo.ctrl)) := by
  rw [field_eq q b n i Z hb hbq hZ hi]
  have h := Compact.PowerTwo.toggle_value q b hb hbq Z (row (n*q) i) (by simp [hZ])
  simpa only [hZ,rowWord,row_rank (n*q) i hi] using h
end IntegerMultBounds.Machine.BinaryParityXorOffsetPositive
