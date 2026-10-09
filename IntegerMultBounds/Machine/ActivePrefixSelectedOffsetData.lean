import IntegerMultBounds.Machine.BinaryPrefixFieldTableData
import IntegerMultBounds.Machine.SelectedSourceBitsStreamData
import IntegerMultBounds.Machine.BinaryVaryingSelectedOffsetData

/-! The actual generated prefix-field tables and batch-extracted controls
drive the first active-target offset load. Controls are bits of the current
full prefix address, not one external source word repeated over the array. -/
namespace IntegerMultBounds.Machine.ActivePrefixSelectedOffsetData
open BinaryVaryingSelectedOffsetData (stream)

def source (W start q f i : ℕ) := Gather.field (BinaryAddressTableData.row W i) start (f*q)
def temp (W start b n i : ℕ) := Gather.field (BinaryAddressTableData.row W i) start (n*b)
def controls (W start q rho n f i : ℕ) := SelectedSourceBitsData.selected (source W start q f i) q rho n

theorem field_bit (xs : List Bool) (start d j : ℕ) (hj : j<d) :
    (Gather.field xs start d).getD j false=xs.getD (start+j) false := by
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simpa using hj),Option.getD_some]
  simp [Gather.field]

/-- Every emitted control is a bit of its own original prefix rank. -/
theorem controls_entry (W start q rho n f i j : ℕ)
    (hnf : n+1=f) (hr : rho<q) (hi : i<2^W) (hj : j<n) :
    (controls W start q rho n f i)[j]'(by simp [controls]; exact hj)=
      Nat.testBit i (start+rho+j*q) := by
  have hinside : rho+j*q<f*q := by
    simpa only [source,Gather.field_length] using SelectedSourceBitsData.selected_inside
      (source W start q f i) q rho n f j (Gather.field_length _ _ _) hnf hr hj
  simp only [controls,SelectedSourceBitsData.selected,List.getElem_map,List.getElem_range,source]
  rw [field_bit _ start (f*q) (rho+j*q) hinside]
  rw [← Compact.PowerTwo.testBit_value,BinaryAddressTableData.row_rank W i hi]
  simp only [Nat.add_assoc]

/-- The physical batch extractor on the physically projected source table
equals the complete varying control stream in exactly prefix-address order. -/
theorem extracted_controls (W start q rho n f : ℕ) (h : start+f*q≤W)
    (hnf : n+1=f) (hr : rho<q) :
    SelectedSourceBitsStreamData.selected (BinaryPrefixFieldTableData.word W start (f*q) h)
      q rho n f (2^W)=stream (2^W) (controls W start q rho n f) := by
  rw [BinaryPrefixFieldTableData.word_rows]
  unfold SelectedSourceBitsStreamData.selected stream controls
  change ((List.range (2^W)).map (fun r => SelectedSourceBitsData.selected
    (((List.range (2^W)).map (fun i => source W start q f i)).flatten) q (r*(f*q)+rho) n)).flatten=
    ((List.range (2^W)).map (fun r => SelectedSourceBitsData.selected (source W start q f r) q rho n)).flatten
  apply congrArg List.flatten
  apply List.map_congr_left
  intro r hr'
  have hrow : r<2^W := List.mem_range.mp hr'
  unfold SelectedSourceBitsData.selected
  apply List.map_congr_left
  intro j hj'
  have hj : j<n := List.mem_range.mp hj'
  have hinside : rho+j*q<f*q := by
    simpa only [source,Gather.field_length] using SelectedSourceBitsData.selected_inside
      (source W start q f r) q rho n f j (Gather.field_length _ _ _) hnf hr hj
  have he := BinaryVaryingSelectedOffsetData.stream_entry (2^W) (f*q)
    (source W start q f) (by intro k hk; exact Gather.field_length _ _ _) r (rho+j*q) hrow hinside
  simpa only [stream,Nat.add_assoc] using he

def offsets (W startT startX q b rho n f : ℕ) (hT : startT+n*b≤W) (hX : startX+f*q≤W)
    (hb : 1≤b) (hbq : b+1≤q) :=
  BinaryVaryingSelectedOffsetGather.word q b hb hbq (BinaryPrefixFieldTableData.word W startT (n*b) hT)
    (SelectedSourceBitsStreamData.selected (BinaryPrefixFieldTableData.word W startX (f*q) hX)
      q rho n f (2^W))

theorem offsets_length (W startT startX q b rho n f : ℕ)
    (hT : startT+n*b≤W) (hX : startX+f*q≤W) (hb : 1≤b) (hbq : b+1≤q) :
    (offsets W startT startX q b rho n f hT hX hb hbq).length=2^W*(n*q) := by
  simp [offsets,Nat.mul_assoc]

/-- The generated offset row uses the current compact temporary and the
selected bits of the current source slot in the unchanged prefix. -/
theorem offset_row (W startT startX q b rho n f i : ℕ)
    (hT : startT+n*b≤W) (hX : startX+f*q≤W) (hb : 1≤b) (hbq : b+1≤q)
    (hnf : n+1=f) (hr : rho<q) (hi : i<2^W) :
    Gather.field (offsets W startT startX q b rho n f hT hX hb hbq) (i*(n*q)) (n*q)=
      Gather.gather (fun x z => x && z) (PackedArith.maskShift q b hb hbq)
        (temp W startT b n i) (controls W startX q rho n f i) n := by
  unfold offsets
  rw [extracted_controls W startX q rho n f hX hnf hr,BinaryPrefixFieldTableData.word_rows]
  exact BinaryVaryingSelectedOffsetData.field_eq q b n (2^W) i (temp W startT b n)
    (controls W startX q rho n f) hb hbq (by intro k hk; exact Gather.field_length _ _ _)
    (by intro k hk; exact SelectedSourceBitsData.selected_length _ _ _ _) hi

end IntegerMultBounds.Machine.ActivePrefixSelectedOffsetData
