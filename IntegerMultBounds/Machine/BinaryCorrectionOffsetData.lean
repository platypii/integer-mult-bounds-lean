import IntegerMultBounds.Machine.BinaryCorrectionOffsetSubtract
import IntegerMultBounds.Machine.BinarySelectedOffsetRepeatData

/-! Exact row operands and modular correction offsets. ControlsAt gathers
are real source-reading operations even though their output ignores the source. -/
namespace IntegerMultBounds.Machine.BinaryCorrectionOffsetData
open BinaryAddressOffsetRepeatData (copies)
open BinarySelectedOffsetData (source controls)

def controlRow (q : ℕ) (Z : List Bool) := (Z.map (fun z => z::List.replicate (q-1) false)).flatten
def controlWord (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :=
  Gather.gather (fun _ z => z) (PackedArith.controlsAt q b hb hbq) (source b n) (controls b n Z) (n*2^(n*b))

theorem controls_gather (q b : ℕ) (Z X : List Bool) (hb : 1≤b) (hbq : b+1≤q) :
    Gather.gather (fun _ z => z) (PackedArith.controlsAt q b hb hbq) X Z Z.length=controlRow q Z := by
  rw [Compact.PowerTwo.gather_flatten]
  have hd (i : ℕ) : Gather.digitWord (fun _ z => z) (PackedArith.controlsAt q b hb hbq) X Z i=
      Z.getD i false::List.replicate (q-1) false := by
    simp [Gather.digitWord,PackedArith.controlsAt,Gather.field]
  rw [funext hd]
  rw [controlRow]
  conv_rhs => rw [Compact.PowerTwo.list_eq_range Z]
  simp only [List.map_map,Function.comp_def]

theorem controlRow_append (q : ℕ) (X Y : List Bool) : controlRow q (X++Y)=controlRow q X++controlRow q Y := by
  simp only [controlRow,List.map_append,List.flatten_append]

theorem controlRow_copies (q : ℕ) (Z : List Bool) (N : ℕ) : controlRow q (copies Z N)=copies (controlRow q Z) N := by
  induction N with
  | zero => rfl
  | succ N ih => rw [BinaryAddressOffsetRepeatData.copies_succ,controlRow_append,ih,BinaryAddressOffsetRepeatData.copies_succ]

theorem controlWord_eq (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (hZ : Z.length=n) :
    controlWord q b n Z hb hbq=copies (controlRow q Z) (2^(n*b)) := by
  unfold controlWord
  rw [←BinarySelectedOffsetData.controls_length b n Z hZ,controls_gather,controls,controlRow_copies]

theorem controlRow_length (q : ℕ) (Z : List Bool) (hq : 0<q) : (controlRow q Z).length=Z.length*q := by
  induction Z with
  | nil => simp [controlRow]
  | cons z Z ih => simp only [controlRow,List.map_cons,List.flatten_cons,List.length_append,List.length_cons,List.length_replicate,Nat.add_mul,Nat.one_mul] at *; omega

def rows (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :=
  (List.range (2^(n*b))).map (fun i => (controlRow q Z,BinarySelectedOffsetValue.rowWord q b n i Z hb hbq))
def word (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :=
  BinaryCorrectionOffsetLoop.result (rows q b n Z hb hbq)

theorem rows_uniform (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (hZ : Z.length=n) :
    BinaryCorrectionOffsetLoop.Uniform (n*q) (rows q b n Z hb hbq) := by
  intro pair hp
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
  exact ⟨by rw [controlRow_length q Z (by omega),hZ],BinarySelectedOffsetValue.rowWord_length _ _ _ _ _ _ _⟩

theorem left_rows (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (hZ : Z.length=n) :
    BinaryCorrectionOffsetLoop.left (rows q b n Z hb hbq)=controlWord q b n Z hb hbq := by
  rw [controlWord_eq q b n Z hb hbq hZ,BinaryAddressOffsetRepeatValue.copies_flatten]
  simp [BinaryCorrectionOffsetLoop.left,rows,List.map_map,Function.comp_def]

theorem right_rows (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (hZ : Z.length=n) :
    BinaryCorrectionOffsetLoop.right (rows q b n Z hb hbq)=BinarySelectedOffsetData.word q b n hb hbq Z := by
  rw [←BinarySelectedOffsetRepeatData.offsets_flatten q b n Z hb hbq hZ]
  simp [BinaryCorrectionOffsetLoop.right,rows,BinarySelectedOffsetRepeatData.offsets,List.map_map,Function.comp_def]

theorem word_length (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (hZ : Z.length=n) :
    (word q b n Z hb hbq).length=2^(n*b)*(n*q) := by
  rw [word,BinaryCorrectionOffsetLoop.result_length (n*q) _ (rows_uniform q b n Z hb hbq hZ)]
  simp [rows]

end IntegerMultBounds.Machine.BinaryCorrectionOffsetData
