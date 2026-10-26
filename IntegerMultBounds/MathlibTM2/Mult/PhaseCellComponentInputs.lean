module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSplitComponentsHost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealCouplingField
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairComponentsAccuracy

/-! Exact component inputs and unchanged magnitude budgets for the two real solves. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

@[simp] theorem value_imagPartWord_re (q : ℕ) (z : GaussianInt) :
    (value q (imagPartWord z)).re = (value q z).im := by simp [value,imagPartWord]

@[simp] theorem value_imagPartWord_im (q : ℕ) (z : GaussianInt) :
    (value q (imagPartWord z)).im = 0 := by simp [value,imagPartWord]

@[simp] theorem value_imagPartWord_norm (q : ℕ) (z : GaussianInt) :
    ‖value q (imagPartWord z)‖ = |(value q z).im| := by
  have h : value q (imagPartWord z) = ((value q z).im : ℂ) := by
    apply Complex.ext <;> simp only [value,imagPartWord,Int.cast_zero,zero_div,Complex.ofReal_re,Complex.ofReal_im]
  rw [h,Complex.norm_real,Real.norm_eq_abs]

theorem componentWords_norm_le (q : ℕ) (z : GaussianInt) :
    ‖value q (realPartWord z)‖ ≤ ‖value q z‖ ∧
      ‖value q (imagPartWord z)‖ ≤ ‖value q z‖ := by
  rw [value_realPartWord_norm,value_imagPartWord_norm]
  exact ⟨Complex.abs_re_le_norm _,Complex.abs_im_le_norm _⟩

theorem componentWords_fits {w : ℕ} {z : GaussianInt} (hz : Fits w z) :
    Fits w (realPartWord z) ∧ Fits w (imagPartWord z) := by
  have hzero : |(0 : ℤ)| < 2^(w-1) := by positivity
  exact ⟨⟨hz.1,hzero⟩,⟨hz.2,hzero⟩⟩

theorem componentInputs_read {A q w s : ℕ} [NeZero s] (hA : 4 ≤ A) (hw : 0 < w)
    (B : ZMod s → GaussianInt) (tailX tailY : List (Fin (A+4))) (i : ZMod s) (hfit : Fits w (B i)) :
    (pairedCellRead q w (cstream A w ((chirpLine s B).map realPartWord)++tailX) i).re =
        (value q (B i)).re ∧
      (pairedCellRead q w (cstream A w ((chirpLine s B).map imagPartWord)++tailY) i).re =
        (value q (B i)).im := by
  have hX : (chirpLine s B).map realPartWord = chirpLine s (fun i => realPartWord (B i)) := by
    simp [chirpLine,List.map_map,Function.comp_def]
  have hY : (chirpLine s B).map imagPartWord = chirpLine s (fun i => imagPartWord (B i)) := by
    simp [chirpLine,List.map_map,Function.comp_def]
  rw [hX,hY,pairedCellRead_encodedField hA hw _ tailX i (componentWords_fits hfit).1,
    pairedCellRead_encodedField hA hw _ tailY i (componentWords_fits hfit).2]
  simp

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

theorem splitComponentLine_spec {s q w e : ℕ} [NeZero s] (hA : 4 ≤ A) (hwidth : q+e+2 ≤ w)
    (B : ZMod s → GaussianInt) (hB : ∀ i, ‖value q (B i)‖ ≤ (2 : ℝ)^e)
    (tail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hs : (S.R 121).length = s) (hw : (S.R 94).length = w)
    (hsrc : S.R 110 = cstream A w (chirpLine s B)++tail)
    (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = []) (h136 : S.R 136 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ splitComponentLineCost s w ∧
      Exec body splitComponentLine (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R
          110 (cstream A w ((chirpLine s B).map realPartWord)++tail))
          137 (cstream A w ((chirpLine s B).map imagPartWord)++S.R 137))}) ∧
      (∀ i, ‖value q (realPartWord (B i))‖ ≤ (2 : ℝ)^e ∧
        ‖value q (imagPartWord (B i))‖ ≤ (2 : ℝ)^e) ∧
      (∀ i, (pairedCellRead q w (cstream A w ((chirpLine s B).map realPartWord)++tail) i).re =
          (value q (B i)).re ∧
        (pairedCellRead q w (cstream A w ((chirpLine s B).map imagPartWord)++S.R 137) i).re =
          (value q (B i)).im) := by
  obtain ⟨v',n,hu,hn,he⟩ := splitComponentLine_exec (body := body) hA s w (chirpLine s B)
    (by simp [chirpLine]) tail v S hs hw hsrc h131 h134 h135 h136
  refine ⟨v',n,hu,hn,he,?_,?_⟩
  · intro i
    exact ⟨(componentWords_norm_le q (B i)).1.trans (hB i),
      (componentWords_norm_le q (B i)).2.trans (hB i)⟩
  · intro i
    exact componentInputs_read hA (by omega) B tail (S.R 137) i (fits_of_value_power hwidth (B i) (hB i))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
