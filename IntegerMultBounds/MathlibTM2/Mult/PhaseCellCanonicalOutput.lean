module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairComponentsAccuracy
public import IntegerMultBounds.MathlibTM2.Node.RoundCall

/-! Replace arbitrary numerator witnesses by the signed values on their actual tapes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.LayerMachine
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.Spec.SignedRingProduct

theorem csyms_symZ (A w : ℕ) (z : GaussianInt) :
    csyms A w (symZ w z) = csyms A w z := by
  simp only [csyms,red_symZ]

theorem decodeWord_csyms_symZ {A w : ℕ} (hA : 4 ≤ A) (hw : 1 ≤ w) (z : GaussianInt) :
    decodeWord (csyms A w z) = symZ w z := by
  rw [←csyms_symZ A w z,decodeWord_csyms hA]
  have hf := topFitsZ_symZ hw z
  rw [compValue_compWord hw hf.1.1 hf.1.2,compValue_compWord hw hf.2.1 hf.2.2]

theorem cstream_symZ (A w : ℕ) (xs : List GaussianInt) :
    cstream A w (xs.map (symZ w)) = cstream A w xs := by
  simp only [cstream,List.flatMap_map,csyms_symZ]

theorem chirpLine_symZ (A w s : ℕ) (G : ZMod s → GaussianInt) :
    cstream A w (chirpLine s (fun i => symZ w (G i))) = cstream A w (chirpLine s G) := by
  have he : chirpLine s (fun i => symZ w (G i)) = (chirpLine s G).map (symZ w) := by
    simp only [chirpLine,List.map_map,Function.comp_def]
  rw [he,cstream_symZ]

theorem pairedCellRead_signed {A w q s : ℕ} [NeZero s] (hA : 4 ≤ A) (hw : 1 ≤ w)
    (G : ZMod s → GaussianInt) (tail : List (Fin (A+4))) (i : ZMod s) :
    pairedCellRead q w (cstream A w (chirpLine s G)++tail) i = value q (symZ w (G i)) := by
  unfold pairedCellRead
  rw [cstream_word w (chirpLine s G) tail i.val (by simpa using i.val_lt)]
  simp only [chirpLine,List.getElem_map,List.getElem_range,ZMod.natCast_zmod_val]
  rw [decodeWord_csyms_symZ hA hw]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
