import IntegerMultBounds.Machine.ActivePrefixDirtyControlSemantics
import IntegerMultBounds.Machine.BinaryCorrectionOffsetSubtract

/-! Independent modular correction rows subtract the selected offset from the
control-mask offset computed at the same complete prefix address. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlCorrectionData
open ActivePrefixDirtyControlData (Shape offsetWord)
open BinaryVaryingSelectedOffsetData (stream)
open BinaryCorrectionOffsetLoop (left right result Uniform)

def controlShape (s : Shape .selected) : Shape .control :=
  ⟨s.W,s.startT,s.startU,s.q,s.b,s.n,by
    change s.startT+s.n*1≤s.W
    have hn := Nat.le_mul_of_pos_right s.n s.hb
    have ht := s.tempFits
    change s.startT+s.n*s.b≤s.W at ht
    omega,s.controlFits,s.hb,s.hbq⟩
def control (s : Shape .selected) := offsetWord (controlShape s)
def selected (s : Shape .selected) := offsetWord s

def rows (s : Shape .selected) := (List.range (2^s.W)).map (fun i =>
  (Gather.field (control s) (i*(s.n*s.q)) (s.n*s.q),
   Gather.field (selected s) (i*(s.n*s.q)) (s.n*s.q)))
def word (s : Shape .selected) := result (rows s)

@[simp] theorem control_length (s : Shape .selected) : (control s).length=2^s.W*(s.n*s.q) :=
  ActivePrefixDirtyControlData.offset_length (controlShape s)
@[simp] theorem selected_length (s : Shape .selected) : (selected s).length=2^s.W*(s.n*s.q) :=
  ActivePrefixDirtyControlData.offset_length s
@[simp] theorem rows_length (s : Shape .selected) : (rows s).length=2^s.W := by simp [rows]

theorem uniform (s : Shape .selected) : Uniform (s.n*s.q) (rows s) := by
  intro pair hp
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
  exact ⟨Gather.field_length _ _ _,Gather.field_length _ _ _⟩

theorem stream_fields (xs : List Bool) (N w : ℕ) (hlen : xs.length=N*w) :
    stream N (fun i => Gather.field xs (i*w) w)=xs := by
  have hl := BinaryVaryingSelectedOffsetData.stream_length N w
    (fun i => Gather.field xs (i*w) w) (by intros; exact Gather.field_length _ _ _)
  apply List.ext_getElem
  · exact hl.trans hlen.symm
  · intro j hj hj'
    have hw : 0<w := by
      by_contra h
      have : w=0 := by omega
      simp_all
    have hjN : j/w<N := (Nat.div_lt_iff_lt_mul hw).mpr (by omega)
    have hjw := Nat.mod_lt j hw
    have he := BinaryVaryingSelectedOffsetData.stream_entry N w
      (fun i => Gather.field xs (i*w) w) (by intros; exact Gather.field_length _ _ _)
      (j/w) (j%w) hjN hjw
    rw [ActivePrefixSelectedOffsetData.field_bit _ _ _ _ hjw] at he
    have hsplit : j/w*w+j%w=j := by simpa only [Nat.mul_comm] using Nat.div_add_mod j w
    rw [hsplit] at he
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,
      List.getElem?_eq_getElem hj',Option.getD_some] using he

theorem left_rows (s : Shape .selected) : left (rows s)=control s := by
  simpa only [left,rows,List.map_map,Function.comp_def,stream] using stream_fields (control s) _ _ (control_length s)
theorem right_rows (s : Shape .selected) : right (rows s)=selected s := by
  simpa only [right,rows,List.map_map,Function.comp_def,stream] using stream_fields (selected s) _ _ (selected_length s)

@[simp] theorem word_length (s : Shape .selected) : (word s).length=2^s.W*(s.n*s.q) := by
  rw [word,BinaryCorrectionOffsetLoop.result_length _ _ (uniform s),rows_length]

theorem field_eq (s : Shape .selected) (i : ℕ) (hi : i<2^s.W) :
    Gather.field (word s) (i*(s.n*s.q)) (s.n*s.q)=
      BinaryCorrectionOffsetRow.diff
        (Gather.field (control s) (i*(s.n*s.q)) (s.n*s.q))
        (Gather.field (selected s) (i*(s.n*s.q)) (s.n*s.q)) := by
  let blocks := (rows s).map (fun x => BinaryCorrectionOffsetRow.diff x.1 x.2)
  have hu := BinaryCorrectionOffsetLoop.result_uniform _ _ (uniform s)
  apply List.ext_getElem
  · simp [BinaryCorrectionOffsetRow.diff,ColumnTransducer.digits_length]
  · intro j hj hj'
    have hjW : j<s.n*s.q := by simpa only [Gather.field_length] using hj
    have hh := BlockRotationData.flatten_index (s.n*s.q) blocks hu i j (by simpa [blocks] using hi) hjW
    simp only [blocks,rows,List.getElem_map,List.getElem_range] at hh
    have he := congrArg (fun x : Option Bool => x.getD false) hh
    change (word s).getD (i*(s.n*s.q)+j) false=
      (BinaryCorrectionOffsetRow.diff
        (Gather.field (control s) (i*(s.n*s.q)) (s.n*s.q))
        (Gather.field (selected s) (i*(s.n*s.q)) (s.n*s.q))).getD j false at he
    have hf := ActivePrefixSelectedOffsetData.field_bit (word s) (i*(s.n*s.q)) (s.n*s.q) j hjW
    rw [he] at hf
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,
      List.getElem?_eq_getElem hj',Option.getD_some] using hf

theorem field_value (s : Shape .selected) (i : ℕ) (hi : i<2^s.W) :
    (Counter.value (Gather.field (word s) (i*(s.n*s.q)) (s.n*s.q)) : ℤ)=
      ((Counter.value (Gather.field (control s) (i*(s.n*s.q)) (s.n*s.q)) : ℤ)-
        Counter.value (Gather.field (selected s) (i*(s.n*s.q)) (s.n*s.q))) % (2 : ℤ)^(s.n*s.q) := by
  rw [field_eq s i hi,BinaryCorrectionOffsetRow.diff,ColumnTransducer.subRule_value _ _
    (by simp),Gather.field_length]

/-- Correction is built from the current compact U parities and current
compact T word at each prefix rank, with independent rowwise subtraction. -/
theorem current_prefix_row (s : Shape .selected) (i : ℕ) (hi : i<2^s.W) :
    Gather.field (word s) (i*(s.n*s.q)) (s.n*s.q)=
      BinaryCorrectionOffsetRow.diff
        (Compact.PowerTwo.toggleMask s.q (ActivePrefixDirtyControlSemantics.controls s i))
        (Gather.gather (fun x z => x && z) (PackedArith.maskShift s.q s.b s.hb s.hbq)
          (ActivePrefixDirtyControlSemantics.tempRow s i)
          (ActivePrefixDirtyControlSemantics.controls s i) s.n) := by
  rw [field_eq s i hi]
  exact congrArg₂ BinaryCorrectionOffsetRow.diff
    (ActivePrefixDirtyControlSemantics.control_row (controlShape s) i hi)
    (ActivePrefixDirtyControlSemantics.selected_row s i hi)

end IntegerMultBounds.Machine.ActivePrefixDirtyControlCorrectionData
