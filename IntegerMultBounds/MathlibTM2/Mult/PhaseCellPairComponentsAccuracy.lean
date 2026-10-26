module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairComponentsHost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputDecode
public import IntegerMultBounds.MathlibTM2.Mult.ChirpCyclicMath

/-! The paired physical output has the two component errors combined once. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem pairComponentWord_fits {w : ℕ} {x y : GaussianInt} (hx : Fits w x) (hy : Fits w y) :
    Fits w (pairComponentWord x y) := ⟨hx.1,hy.1⟩

@[simp] theorem value_pairComponentWord_re (q : ℕ) (x y : GaussianInt) :
    (value q (pairComponentWord x y)).re = (value q x).re := by
  simp [value,pairComponentWord]

@[simp] theorem value_pairComponentWord_im (q : ℕ) (x y : GaussianInt) :
    (value q (pairComponentWord x y)).im = (value q y).re := by
  simp [value,pairComponentWord]

noncomputable def pairedCellRead {A : ℕ} (q w : ℕ) (raw : List (Fin (A+4))) (i : ZMod s) : ℂ :=
  value q (decodeWord ((raw.drop (i.val*w)).take w))

theorem pairedCellRead_encodedField {A w q s : ℕ} [NeZero s] (hA : 4 ≤ A) (hw : 0 < w)
    (C : ZMod s → GaussianInt) (tail : List (Fin (A+4))) (i : ZMod s) (hfit : Fits w (C i)) :
    pairedCellRead q w (cstream A w (chirpLine s C)++tail) i = value q (C i) := by
  simp only [pairedCellRead]
  rw [cstream_word w (chirpLine s C) tail i.val (by simpa using i.val_lt)]
  simp only [chirpLine,List.getElem_map,List.getElem_range,ZMod.natCast_zmod_val]
  rw [decodeWord_of_fits hA hw _ hfit]

theorem pairedComponents_accuracy {A w q s : ℕ} [NeZero s] (hA : 4 ≤ A) (hw : 0 < w)
    (X Y : ZMod s → GaussianInt) (active : Finset (ZMod s))
    (hXfit : ∀ i ∈ active, Fits w (X i)) (hYfit : ∀ i ∈ active, Fits w (Y i)) (z : ZMod s → ℂ) (eX eY : ℝ)
    (hX : PhaseCellInterface.ErrorOn active (fun i => (value q (X i)).re) (fun i => (z i).re) eX)
    (hY : PhaseCellInterface.ErrorOn active (fun i => (value q (Y i)).re) (fun i => (z i).im) eY)
    (tail : List (Fin (A+4))) :
    PhaseCellInterface.ErrorOn active
      (pairedCellRead q w (cstream A w (chirpLine s (fun i => pairComponentWord (X i) (Y i)))++tail))
      z (eX+eY) := by
  intro i hi
  rw [pairedCellRead_encodedField hA hw _ tail i (pairComponentWord_fits (hXfit i hi) (hYfit i hi))]
  have hnorm := Complex.norm_le_abs_re_add_abs_im (value q (pairComponentWord (X i) (Y i))-z i)
  have hx := hX i hi
  have hy := hY i hi
  simp only [Complex.sub_re,Complex.sub_im,value_pairComponentWord_re,value_pairComponentWord_im,
    Real.norm_eq_abs] at hnorm hx hy
  exact hnorm.trans (add_le_add hx hy)

theorem pairComponentWords_chirpLine {s : ℕ} [NeZero s] (X Y : ZMod s → GaussianInt) :
    List.zipWith pairComponentWord (chirpLine s X) (chirpLine s Y) =
      chirpLine s (fun i => pairComponentWord (X i) (Y i)) := by
  simp [chirpLine,List.zipWith_map,List.zipWith_self]

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

theorem pairComponentLines_spec {s w q : ℕ} [NeZero s] (hA : 4 ≤ A) (hw : 0 < w)
    (X Y : ZMod s → GaussianInt) (active : Finset (ZMod s))
    (hXfit : ∀ i ∈ active, Fits w (X i)) (hYfit : ∀ i ∈ active, Fits w (Y i))
    (z : ZMod s → ℂ) (eX eY : ℝ)
    (hX : PhaseCellInterface.ErrorOn active (fun i => (value q (X i)).re) (fun i => (z i).re) eX)
    (hY : PhaseCellInterface.ErrorOn active (fun i => (value q (Y i)).re) (fun i => (z i).im) eY)
    (tailX tailY : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hs : (S.R 121).length = s) (hwidth : (S.R 94).length = w)
    (hx : S.R 132 = cstream A w (chirpLine s X)++tailX)
    (hy : S.R 137 = cstream A w (chirpLine s Y)++tailY)
    (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = []) (h140 : S.R 140 = []) :
    let G := fun i => pairComponentWord (X i) (Y i)
    ∃ v' n, v'.user = v.user ∧ n ≤ pairComponentLinesCost s w ∧
      Exec body pairComponentLines (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 137 tailY)
          132 (cstream A w (chirpLine s G)++tailX))}) ∧
      PhaseCellInterface.ErrorOn active
        (pairedCellRead q w (cstream A w (chirpLine s G)++tailX)) z (eX+eY) := by
  dsimp only
  obtain ⟨v',n,hu,hn,he⟩ := pairComponentLines_exec (body := body) hA s w (chirpLine s X) (chirpLine s Y)
    (by simp [chirpLine]) (by simp [chirpLine]) tailX tailY v S hs hwidth hx hy h131 h134 h135 h140
  refine ⟨v',n,hu,hn,?_,pairedComponents_accuracy hA hw X Y active hXfit hYfit z eX eY hX hY tailX⟩
  simpa only [pairComponentWords_chirpLine] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
