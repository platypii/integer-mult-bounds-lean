import IntegerMultBounds.Machine.BinaryVaryingSelectedOffsetData
import IntegerMultBounds.Machine.ActivePrefixSelectedOffsetData

/-! Gathering from concatenated source and control rows preserves the original
row boundaries. Both inputs may vary independently with the physical rank. -/
namespace IntegerMultBounds.Machine.GatherStreamData
open BinaryVaryingSelectedOffsetData (stream stream_length stream_entry)

/-- Fixed-width physical fields reconstruct the complete original word,
including zero-width rows. -/
theorem stream_fields (xs : List Bool) (N w : ℕ) (hl : xs.length=N*w) :
    stream N (fun i => Gather.field xs (i*w) w)=xs := by
  have hlen := stream_length N w (fun i => Gather.field xs (i*w) w)
    (by intro i hi; exact Gather.field_length _ _ _)
  apply List.ext_getElem
  · exact hlen.trans hl.symm
  · intro k hk hk'
    have hkw : k<N*w := by omega
    have hp : 0<w := by
      by_contra h
      have hw : w=0 := by omega
      rw [hw,Nat.mul_zero] at hkw
      omega
    have hi : k/w<N := (Nat.div_lt_iff_lt_mul hp).mpr hkw
    have hj : k%w<w := Nat.mod_lt _ hp
    have h := stream_entry N w (fun i => Gather.field xs (i*w) w)
      (by intro i hi; exact Gather.field_length _ _ _) (k/w) (k%w) hi hj
    rw [ActivePrefixSelectedOffsetData.field_bit] at h
    · have he : k/w*w+k%w=k := by simpa only [Nat.mul_comm] using Nat.div_add_mod k w
      rw [he] at h
      simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk,
        List.getElem?_eq_getElem hk',Option.getD_some] using h
    · exact hj

private theorem gather_bit (op : Bool → Bool → Bool) (S : Gather.Shape) (X Z : List Bool) (N k r : ℕ)
    (hk : k<N) (hr : r<S.st) :
    (Gather.gather op S X Z N).getD (k*S.st+r) false=
      (Gather.digitWord op S X Z k).getD r false := by
  have h := BlockRotationData.flatten_index S.st
    ((List.range N).map (Gather.digitWord op S X Z))
    (by intro xs hx; obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx; exact Gather.digitWord_length _ _ _ _ _)
    k r (by simpa using hk) hr
  rw [Compact.PowerTwo.gather_flatten,List.getD_eq_getElem?_getD,h]
  simp only [List.getElem_map,List.getElem_range,List.getD_eq_getElem?_getD]

private theorem digit_eq (op : Bool → Bool → Bool) (S : Gather.Shape) (n N i j : ℕ)
    (X Z : ℕ → List Bool)
    (hx : ∀ k<N, (X k).length=n*S.sx) (hz : ∀ k<N, (Z k).length=n)
    (hi : i<N) (hj : j<n) :
    Gather.digitWord op S (stream N X) (stream N Z) (i*n+j)=
      Gather.digitWord op S (X i) (Z i) j := by
  simp only [Gather.digitWord]
  rw [stream_entry N n Z hz i j hi hj]
  have he : Gather.field (stream N X) ((i*n+j)*S.sx+S.ox) S.d=
      Gather.field (X i) (j*S.sx+S.ox) S.d := by
    unfold Gather.field
    apply List.map_congr_left
    intro r hr
    have hr' := List.mem_range.mp hr
    have hinside : j*S.sx+S.ox+r<n*S.sx := by
      have hs := S.hx
      have hmul := Nat.mul_le_mul_right S.sx (show j+1≤n by omega)
      nlinarith
    have h := stream_entry N (n*S.sx) X hx i (j*S.sx+S.ox+r) hi hinside
    simpa only [Nat.add_mul,Nat.mul_assoc,Nat.add_assoc] using h
  rw [he]

/-- Every output row is the gather of the corresponding original input rows. -/
theorem field_eq (op : Bool → Bool → Bool) (S : Gather.Shape) (hpos : 0<S.st)
    (n N i : ℕ) (X Z : ℕ → List Bool)
    (hx : ∀ k<N, (X k).length=n*S.sx) (hz : ∀ k<N, (Z k).length=n) (hi : i<N) :
    Gather.field (Gather.gather op S (stream N X) (stream N Z) (stream N Z).length)
      (i*(n*S.st)) (n*S.st)=Gather.gather op S (X i) (Z i) n := by
  have hlen := stream_length N n Z hz
  apply List.ext_getElem
  · simp [Gather.gather_length]
  · intro r hr hr'
    have hrn : r<n*S.st := by simpa only [Gather.field_length] using hr
    have hk : r/S.st<n := (Nat.div_lt_iff_lt_mul hpos).mpr hrn
    have hm : r%S.st<S.st := Nat.mod_lt _ hpos
    have hbig : i*n+r/S.st<N*n := by nlinarith
    have hsplit : r/S.st*S.st+r%S.st=r := by simpa only [Nat.mul_comm] using Nat.div_add_mod r S.st
    have hindex : i*(n*S.st)+r=(i*n+r/S.st)*S.st+r%S.st := by nlinarith
    have hl := gather_bit op S (stream N X) (stream N Z) (N*n) (i*n+r/S.st) (r%S.st) hbig hm
    have hh := gather_bit op S (X i) (Z i) n (r/S.st) (r%S.st) hk hm
    rw [digit_eq op S n N i (r/S.st) X Z hx hz hi hk] at hl
    rw [hsplit] at hh
    rw [←hindex] at hl
    have hout : (Gather.gather op S (stream N X) (stream N Z) (stream N Z).length).getD
        (i*(n*S.st)+r) false=(Gather.digitWord op S (X i) (Z i) (r/S.st)).getD (r%S.st) false := by
      rw [hlen]
      exact hl
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hr',Option.getD_some] at hh
    simp only [Gather.field,List.getElem_map,List.getElem_range]
    exact hout.trans hh.symm

end IntegerMultBounds.Machine.GatherStreamData
