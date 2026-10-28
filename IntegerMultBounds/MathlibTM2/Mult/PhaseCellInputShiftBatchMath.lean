module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputShiftInverse
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoundBatchWords

/-! Exact conversion and retraction laws for an arbitrary ordered complex batch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {s : ℕ}

def inputShiftField (d : ℕ) (F : ZMod s → GaussianInt) : ZMod s → GaussianInt :=
  fun i => (2 : GaussianInt)^d*F i

def inputUnshiftField (d : ℕ) (F : ZMod s → GaussianInt) : ZMod s → GaussianInt :=
  fun i => tdivN d (F i)

theorem inputUnshiftField_shift (d : ℕ) (F : ZMod s → GaussianInt) :
    inputUnshiftField d (inputShiftField d F) = F := by
  funext i
  exact inputShift_tdiv d (F i)

theorem inputShiftField_flatten (d : ℕ) (Fs : List (ZMod s → GaussianInt)) :
    ((Fs.map (chirpLine s)).flatten).map (fun z => (2 : GaussianInt)^d*z) =
      ((Fs.map (inputShiftField d)).map (chirpLine s)).flatten := by
  induction Fs with
  | nil => rfl
  | cons F Fs ih =>
    simp only [List.map_cons,List.flatten_cons,List.map_append,ih]
    congr 1
    simp only [chirpLine,List.map_map,Function.comp_def,inputShiftField]

theorem inputShiftField_value (p d : ℕ) (F : ZMod s → GaussianInt) (i : ZMod s) :
    value (p+1+d) (inputShiftField d F i) = (1/2 : ℂ)*value p (F i) :=
  halfGrid_value p d (F i)

theorem inputBatch_unit (p : ℕ) (Fs : List (ZMod s → GaussianInt))
    (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1) :
    ∀ z ∈ (Fs.map (chirpLine s)).flatten, ‖value p z‖ ≤ 1 := by
  intro z hz
  obtain ⟨zs,hzs,hz⟩ := List.mem_flatten.mp hz
  obtain ⟨F,hFmem,rfl⟩ := List.mem_map.mp hzs
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hz
  exact hF F hFmem (i : ZMod s)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
