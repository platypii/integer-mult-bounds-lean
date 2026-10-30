module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInputShiftHeader

/-! The executed local conversion matches ordered packed numerical RHS fields. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

/-- Pointwise field conversion commutes with local interval storage. -/
theorem packedInterval_map {s : ℕ} (a L : ℕ) (F : ZMod s → GaussianInt)
    (g : GaussianInt → GaussianInt) :
    (packedInterval a L F).map g = packedInterval a L (fun i => g (F i)) := by
  simp [packedInterval,chirpLine,List.map_take,List.map_drop,List.map_map,Function.comp_def]

theorem packedBatch_map {s : ℕ} (a L : ℕ) (Fs : List (ZMod s → GaussianInt))
    (g : GaussianInt → GaussianInt) :
    ((Fs.map (packedInterval a L)).flatten).map g =
      (Fs.map (fun F => packedInterval a L (fun i => g (F i)))).flatten := by
  induction Fs with
  | nil => simp
  | cons F Fs ih => simp [ih,packedInterval_map]

theorem cstream_flatten (A w : ℕ) (xs : List (List GaussianInt)) :
    cstream A w xs.flatten = (xs.map (cstream A w)).flatten := by
  induction xs with
  | nil => simp
  | cons zs xs ih => simp [ih]

/-- The converted flat word is exactly the per-replica source ABI used by the
packed batch supplier, in the same replica order. -/
theorem packedBatch_shift_source {s : ℕ} (A w d a L : ℕ) (Fs : List (ZMod s → GaussianInt)) :
    cstream A w (((Fs.map (packedInterval a L)).flatten).map (fun z => (2 : GaussianInt)^d*z)) =
      (Fs.map (fun F => cstream A w (packedInterval a L (fun i => (2 : GaussianInt)^d*F i)))).flatten := by
  rw [packedBatch_map,cstream_flatten]
  simp only [List.map_map,Function.comp_def]

/-- Only the local halo length enters the converted batch size. -/
theorem packedBatch_length {s : ℕ} (a L : ℕ) (Fs : List (ZMod s → GaussianInt))
    (hfit : a+L ≤ s) : (Fs.map (packedInterval a L)).flatten.length = Fs.length*L := by
  induction Fs with
  | nil => simp
  | cons F Fs ih => simp [ih,packedInterval_length F hfit,Nat.add_mul,Nat.add_comm]

/-- Unit p-grid inputs automatically meet the packed supplier's numerical RHS
bound after conversion, for every nonnegative requested RHS exponent. -/
theorem packedBatch_shift_bound {s : ℕ} (p q rhsExp : ℕ) (hp : p+1 ≤ q)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1) :
    ∀ F ∈ Fs, ∀ i, ‖value q ((2 : GaussianInt)^(q-p-1)*F i)‖ ≤ (2 : ℝ)^rhsExp := by
  intro F hmem i
  rw [(packedInputShift_value_fits p q hp (F i) (hF F hmem i)).1,norm_mul]
  have hnorm : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by norm_num
  rw [hnorm]
  have hpow : (1 : ℝ) ≤ 2^rhsExp := one_le_pow₀ (by norm_num)
  have hunit := hF F hmem i
  nlinarith

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
