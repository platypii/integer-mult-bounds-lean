import IntegerMultBounds.Machine.BinaryVaryingSelectedOffsetGather
import IntegerMultBounds.Machine.BinarySelectedOffsetValue

/-! Per-prefix semantics of the varying-control physical gather. Neither
source digits nor controls must repeat: both are read from their current row.
This is the mask-shift load needed when source bits vary with the address. -/
namespace IntegerMultBounds.Machine.BinaryVaryingSelectedOffsetData

def stream (N : ℕ) (rows : ℕ → List Bool) := ((List.range N).map rows).flatten

theorem stream_length (N w : ℕ) (rows : ℕ → List Bool)
    (hw : ∀ i<N, (rows i).length=w) : (stream N rows).length=N*w := by
  unfold stream
  rw [BlockRotationData.uniform_volume w]
  · simp
  · intro xs hx
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    exact hw i (List.mem_range.mp hi)

theorem stream_entry (N w : ℕ) (rows : ℕ → List Bool)
    (hw : ∀ i<N, (rows i).length=w) (i j : ℕ) (hi : i<N) (hj : j<w) :
    (stream N rows).getD (i*w+j) false=(rows i).getD j false := by
  have h := BlockRotationData.flatten_index w ((List.range N).map rows)
    (by intro xs hx; obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hx; exact hw k (List.mem_range.mp hk))
    i j (by simpa using hi) hj
  simp only [List.getElem_map,List.getElem_range] at h
  simpa only [stream,List.getD_eq_getElem?_getD] using congrArg (fun z => z.getD false) h

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

private theorem digit_eq (q b n N i j : ℕ) (X Z : ℕ → List Bool)
    (hb : 1≤b) (hbq : b+1≤q)
    (hx : ∀ k<N, (X k).length=n*b) (hz : ∀ k<N, (Z k).length=n)
    (hi : i<N) (hj : j<n) :
    Gather.digitWord (fun x z => x && z) (PackedArith.maskShift q b hb hbq)
      (stream N X) (stream N Z) (i*n+j)=
    Gather.digitWord (fun x z => x && z) (PackedArith.maskShift q b hb hbq) (X i) (Z i) j := by
  simp only [Gather.digitWord,PackedArith.maskShift,Nat.add_zero]
  rw [stream_entry N n Z hz i j hi hj]
  have he : Gather.field (stream N X) ((i*n+j)*b) b=Gather.field (X i) (j*b) b := by
    unfold Gather.field
    apply List.map_congr_left
    intro r hr
    have h := stream_entry N (n*b) X hx i (j*b+r) hi (by have := List.mem_range.mp hr; nlinarith)
    simpa only [Nat.add_mul,Nat.mul_assoc,Nat.add_assoc] using h
  rw [he]

/-- Each physical output row uses its own current source and control words. -/
theorem field_eq (q b n N i : ℕ) (X Z : ℕ → List Bool)
    (hb : 1≤b) (hbq : b+1≤q)
    (hx : ∀ k<N, (X k).length=n*b) (hz : ∀ k<N, (Z k).length=n) (hi : i<N) :
    Gather.field (BinaryVaryingSelectedOffsetGather.word q b hb hbq (stream N X) (stream N Z))
      (i*(n*q)) (n*q)=
    Gather.gather (fun x z => x && z) (PackedArith.maskShift q b hb hbq) (X i) (Z i) n := by
  have hlen := stream_length N n Z hz
  apply List.ext_getElem
  · simp [Gather.gather_length,PackedArith.maskShift]
  · intro r hr hr'
    have hrn : r<n*q := by simpa only [Gather.field_length] using hr
    have hk : r/q<n := (Nat.div_lt_iff_lt_mul (by omega)).mpr hrn
    have hm : r%q<q := Nat.mod_lt _ (by omega)
    have hbig : i*n+r/q<N*n := by nlinarith
    have hsplit : r/q*q+r%q=r := by simpa only [Nat.mul_comm] using Nat.div_add_mod r q
    have hindex : i*(n*q)+r=(i*n+r/q)*q+r%q := by nlinarith
    have hl := gather_bit (PackedArith.maskShift q b hb hbq) (stream N X) (stream N Z)
      (N*n) (i*n+r/q) (r%q) hbig hm
    have hh := gather_bit (PackedArith.maskShift q b hb hbq) (X i) (Z i) n (r/q) (r%q) hk hm
    rw [digit_eq q b n N i (r/q) X Z hb hbq hx hz hi hk] at hl
    dsimp only [PackedArith.maskShift] at hl hh
    rw [hsplit] at hh
    rw [←hindex] at hl
    have hout : (BinaryVaryingSelectedOffsetGather.word q b hb hbq (stream N X) (stream N Z)).getD
        (i*(n*q)+r) false=
        (Gather.digitWord (fun x z => x && z) (PackedArith.maskShift q b hb hbq) (X i) (Z i)
          (r/q)).getD (r%q) false := by
      unfold BinaryVaryingSelectedOffsetGather.word
      rw [hlen]
      exact hl
    change (Gather.gather (fun x z => x && z) (PackedArith.maskShift q b hb hbq) (X i) (Z i) n).getD
      r false=(Gather.digitWord (fun x z => x && z) (PackedArith.maskShift q b hb hbq) (X i) (Z i)
        (r/q)).getD (r%q) false at hh
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hr',Option.getD_some] at hh
    simp only [Gather.field,List.getElem_map,List.getElem_range]
    exact hout.trans hh.symm

/-- With each compact field supplied by its actual binary address word, the
physical output offset has the required packed two-times-control product. -/
theorem field_value (q b n N i : ℕ) (T : ℕ → Fin (2^(n*b))) (Z : ℕ → List Bool)
    (hb : 1≤b) (hbq : b+1≤q) (hz : ∀ k<N, (Z k).length=n) (hi : i<N) :
    (Counter.value (Gather.field
      (BinaryVaryingSelectedOffsetGather.word q b hb hbq
        (stream N (fun k => BinaryAddressTableData.row (n*b) (T k).val)) (stream N Z))
      (i*(n*q)) (n*q)) : ℤ)=
    Compact.Radix.pack ((2 : ℤ)^q) (List.zipWith (fun z w => 2*z*w)
      ((Z i).map Compact.PowerTwo.ctrl) (Compact.Radix.digits ((2 : ℤ)^b) n (T i).val)) := by
  rw [field_eq q b n N i _ Z hb hbq (by intro k hk; exact BinaryAddressTableData.row_length _ _) hz hi]
  have h := Compact.PowerTwo.maskShift_value q b hb hbq (Z i)
    (BinaryAddressTableData.row (n*b) (T i).val) (by simp [hz i hi])
  simpa only [hz i hi,BinaryAddressTableData.row_rank (n*b) (T i).val (T i).isLt] using h

end IntegerMultBounds.Machine.BinaryVaryingSelectedOffsetData
