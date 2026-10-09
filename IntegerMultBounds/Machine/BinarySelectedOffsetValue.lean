import IntegerMultBounds.Machine.BinarySelectedOffset
import IntegerMultBounds.Compact.PackedArithValue

/-! The physically generated selected offset row is exactly the packed
2*z*w load from the first line of the early-source gadget. -/
namespace IntegerMultBounds.Machine.BinarySelectedOffsetValue
open BinarySelectedOffsetData BinaryAddressTableData
open BinaryAddressOffsetRepeatData (copies)

private theorem copies_replicate (Z : List Bool) (N : ℕ) : copies Z N=(List.replicate N Z).flatten := by
  induction N with
  | zero => rfl
  | succ N ih => simp [BinaryAddressOffsetRepeatData.copies_succ,List.replicate_add,ih]

theorem controls_entry (b n i j : ℕ) (Z : List Bool) (hZ : Z.length=n)
    (hi : i<2^(n*b)) (hj : j<n) :
    (controls b n Z).getD (i*n+j) false=Z.getD j false := by
  have h := BlockRotationData.flatten_index n (List.replicate (2^(n*b)) Z)
    (by intro xs hx; obtain ⟨_,rfl⟩ := List.mem_replicate.mp hx; exact hZ)
    i j (by simpa using hi) hj
  rw [controls,copies_replicate,List.getD_eq_getElem?_getD,h]
  simp only [List.getElem_replicate,List.getD_eq_getElem?_getD]

private theorem source_field (b n i j : ℕ) (_hb : 0<b) (hi : i<2^(n*b)) (hj : j<n) :
    Gather.field (source b n) ((i*n+j)*b) b=Gather.field (row (n*b) i) (j*b) b := by
  unfold Gather.field
  apply List.map_congr_left
  intro r hr
  have hrlt := List.mem_range.mp hr
  have h := BinaryAddressOffsetData.table_entry (n*b) (2^(n*b)) i (j*b+r) hi (by nlinarith)
  change (BinaryAddressOffsetData.source b n).getD ((i*n+j)*b+r) false=_
  simpa only [BinaryAddressOffsetData.source,Nat.add_mul,Nat.mul_assoc,Nat.add_assoc] using h

private theorem digit_eq (q b n i j : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q)
    (hZ : Z.length=n) (hi : i<2^(n*b)) (hj : j<n) :
    Gather.digitWord (fun x z => x && z) (PackedArith.maskShift q b hb hbq)
      (source b n) (controls b n Z) (i*n+j)=
    Gather.digitWord (fun x z => x && z) (PackedArith.maskShift q b hb hbq)
      (row (n*b) i) Z j := by
  simp only [Gather.digitWord,PackedArith.maskShift,Nat.add_zero]
  rw [source_field b n i j (by omega) hi hj,controls_entry b n i j Z hZ hi hj]

private theorem gather_bit (S : Gather.Shape) (X Z : List Bool) (N k r : ℕ)
    (hk : k<N) (hr : r<S.st) :
    (Gather.gather (fun x z => x && z) S X Z N).getD (k*S.st+r) false=
      (Gather.digitWord (fun x z => x && z) S X Z k).getD r false := by
  have h := BlockRotationData.flatten_index S.st
    ((List.range N).map (Gather.digitWord (fun x z => x && z) S X Z))
    (by intro xs hx; obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx; exact Gather.digitWord_length _ _ _ _ _)
    k r (by simpa using hk) hr
  rw [Compact.PowerTwo.gather_flatten,List.getD_eq_getElem?_getD,h]
  simp only [List.getElem_map,List.getElem_range,List.getD_eq_getElem?_getD]

def rowWord (q b n i : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :=
  Gather.gather (fun x z => x && z) (PackedArith.maskShift q b hb hbq) (row (n*b) i) Z n
@[simp] theorem rowWord_length (q b n i : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :
    (rowWord q b n i Z hb hbq).length=n*q := Gather.gather_length _ _ _ _ _

/-- Each generated row uses exactly the original control word, independently
of the regular temporary address; no repeated-control input is assumed. -/
theorem field_eq (q b n i : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q)
    (hZ : Z.length=n) (hi : i<2^(n*b)) :
    Gather.field (word q b n hb hbq Z) (i*(n*q)) (n*q)=rowWord q b n i Z hb hbq := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    have hjn : j<n*q := by simpa only [Gather.field_length] using hj
    have hk : j/q<n := (Nat.div_lt_iff_lt_mul (by omega)).mpr hjn
    have hr : j%q<q := Nat.mod_lt _ (by omega)
    have hbig : i*n+j/q<n*2^(n*b) := by nlinarith
    have hsplit : (j/q)*q+j%q=j := by simpa only [Nat.mul_comm] using Nat.div_add_mod j q
    have hindex : i*(n*q)+j=(i*n+j/q)*q+j%q := by nlinarith
    have hl := gather_bit (PackedArith.maskShift q b hb hbq) (source b n) (controls b n Z)
      (n*2^(n*b)) (i*n+j/q) (j%q) hbig hr
    have hh := gather_bit (PackedArith.maskShift q b hb hbq) (row (n*b) i) Z n (j/q) (j%q) hk hr
    rw [digit_eq q b n i (j/q) Z hb hbq hZ hi hk] at hl
    dsimp only [PackedArith.maskShift] at hl hh
    rw [hsplit] at hh
    rw [←hindex] at hl
    change (word q b n hb hbq Z).getD (i*(n*q)+j) false=_ at hl
    change (rowWord q b n i Z hb hbq).getD j false=_ at hh
    simp only [Gather.field,List.getElem_map,List.getElem_range]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj',Option.getD_some] at hh
    exact hl.trans hh.symm

theorem field_value (q b n i : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q)
    (hZ : Z.length=n) (hi : i<2^(n*b)) :
    (Counter.value (Gather.field (word q b n hb hbq Z) (i*(n*q)) (n*q)) : ℤ)=
      Compact.Radix.pack ((2 : ℤ)^q) (List.zipWith (fun z w => 2*z*w) (Z.map Compact.PowerTwo.ctrl)
        (Compact.Radix.digits ((2 : ℤ)^b) n i)) := by
  rw [field_eq q b n i Z hb hbq hZ hi]
  have h := Compact.PowerTwo.maskShift_value q b hb hbq Z (row (n*b) i) (by simp [hZ])
  simpa only [hZ,rowWord,row_rank (n*b) i hi] using h
end IntegerMultBounds.Machine.BinarySelectedOffsetValue
