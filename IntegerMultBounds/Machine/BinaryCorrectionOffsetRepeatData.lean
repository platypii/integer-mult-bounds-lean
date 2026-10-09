import IntegerMultBounds.Machine.BinaryCorrectionOffsetValue
import IntegerMultBounds.Machine.BinaryAddressOffsetRepeatValue

/-! The literal table repeated by the selected mask-shift offset constructor. -/
namespace IntegerMultBounds.Machine.BinaryCorrectionOffsetRepeatData
open BinaryAddressOffsetRepeatData (copies expanded)

def offsets (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :=
  (List.range (2^(n*b))).map (fun i => BinaryCorrectionOffsetValue.rowWord q b n i Z hb hbq)
def destination (q b n L K : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :=
  copies (expanded (offsets q b n Z hb hbq) L) K

/-- The base producer's literal word is precisely the concatenation of its
per-address offset fields; no alternate table representation is assumed. -/
theorem offsets_flatten (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (hZ : Z.length=n) :
    (offsets q b n Z hb hbq).flatten=BinaryCorrectionOffsetData.word q b n Z hb hbq := by
  let blocks := offsets q b n Z hb hbq
  have hu : BlockRotationData.Uniform (n*q) blocks := by
    intro xs hx; obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx; exact BinaryCorrectionOffsetValue.rowWord_length _ _ _ _ _ _ _ hZ
  have hlen : blocks.length=2^(n*b) := by simp [blocks,offsets]
  apply List.ext_getElem
  · rw [BlockRotationData.uniform_volume (n*q) blocks hu,hlen,BinaryCorrectionOffsetData.word_length q b n Z hb hbq hZ]
  · intro j hj hj'
    have hjv : j<(2^(n*b))*(n*q) := by
      have hjb : j<blocks.flatten.length := hj
      rw [BlockRotationData.uniform_volume (n*q) blocks hu,hlen] at hjb
      exact hjb
    have hW : 0<n*q := by nlinarith
    have hi : j/(n*q)<2^(n*b) := (Nat.div_lt_iff_lt_mul hW).mpr hjv
    have hr : j%(n*q)<n*q := Nat.mod_lt _ hW
    have he : j/(n*q)*(n*q)+j%(n*q)=j := by simpa only [Nat.mul_comm] using Nat.div_add_mod j (n*q)
    have hh := BlockRotationData.flatten_index (n*q) blocks hu (j/(n*q)) (j%(n*q)) (by omega) hr
    rw [he,List.getElem?_eq_getElem hj] at hh
    have hf := congrArg (fun xs : List Bool => xs[j%(n*q)]?)
      (BinaryCorrectionOffsetValue.field_eq q b n (j/(n*q)) Z hb hbq hZ hi)
    rw [List.getElem?_eq_getElem (by simpa using hr)] at hf
    simp only [Gather.field,List.getElem_map,List.getElem_range,List.getD_eq_getElem?_getD,he,
      List.getElem?_eq_getElem hj',Option.getD_some] at hf
    change some (blocks.flatten[j]'hj)=_ at hh
    simp only [blocks,offsets,List.getElem_map,List.getElem_range] at hh
    exact Option.some.inj (hh.trans hf.symm)

theorem offsets_uniform (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (hZ : Z.length=n) :
    BlockRotationData.Uniform (n*q) (offsets q b n Z hb hbq) := by
  intro xs hx; obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx; exact BinaryCorrectionOffsetValue.rowWord_length _ _ _ _ _ _ _ hZ

end IntegerMultBounds.Machine.BinaryCorrectionOffsetRepeatData
