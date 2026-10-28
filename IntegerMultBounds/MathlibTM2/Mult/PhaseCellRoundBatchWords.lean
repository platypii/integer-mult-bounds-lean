module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFinalRoundList

/-! Connect one flat rounding pass to the ordered complex fields of a batch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {s : ℕ}

theorem roundBatchWords_flatten (w q p j : ℕ) (Gs : List (ZMod s → GaussianInt)) :
    ((Gs.map (chirpLine s)).flatten).map (finalRoundWord w q p j) =
      ((Gs.map (fun G i => finalRoundWord w q p j (G i))).map (chirpLine s)).flatten := by
  induction Gs with
  | nil => rfl
  | cons G Gs ih =>
    simp only [List.map_cons,List.flatten_cons,List.map_append,ih]
    congr 1
    simp only [chirpLine,List.map_map,Function.comp_def]

variable [NeZero s]

theorem roundBatchField_decoded {A w q p j E : ℕ} (hA : 4 ≤ A) (hw : 1 ≤ w)
    (hp : p ≤ q) (G : ZMod s → GaussianInt)
    (tail : List (Fin (A+4))) (i : ZMod s)
    (hG : ‖pairedCellRead q w (cstream A w (chirpLine s G)) i‖ ≤ 8*(2 : ℝ)^E) :
    pairedCellRead p (p+E+5)
      (cstream A (p+E+5) (chirpLine s (fun k => finalRoundWord w q p j (G k)))++tail) i =
      rhoC p (((2 : ℂ)^j)⁻¹*pairedCellRead q w (cstream A w (chirpLine s G)) i) := by
  have hr := pairedCellRead_signed (q := q) hA hw G [] i
  rw [List.append_nil] at hr
  have hb : ‖value q (symZ w (G i))‖ ≤ 8*(2 : ℝ)^E := by rw [←hr]; exact hG
  have hf := finalRound_fits q p j E (p+E+5) hp le_rfl _ hb
  have hd := pairedCellRead_encodedField (q := p) hA (show 0 < p+E+5 by omega)
    (fun k => finalRoundWord w q p j (G k)) tail i hf
  rw [hd,hr]
  exact value_finalRound q p j hp _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
