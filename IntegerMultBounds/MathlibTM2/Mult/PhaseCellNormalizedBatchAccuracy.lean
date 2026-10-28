module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoundBatchWords
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoundMagnitudeSelection
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryExactBounds

/-! Uniform normalized error for an ordered batch, including clipped active sets. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {s : ℕ} [NeZero s]

theorem roundedField_accuracy {A w q p j target : ℕ} (hA : 4 ≤ A) (hw : 1 ≤ w) (hp : p ≤ q)
    (active : Finset (ZMod s)) (G : ZMod s → GaussianInt) (x : ZMod s → ℂ)
    (hx : ∀ i ∈ active, ‖x i‖ ≤ 64*(p : ℝ))
    (he : PhaseCellInterface.ErrorOn active (pairedCellRead q w (cstream A w (chirpLine s G))) x
      (1/(2 : ℝ)^target)) :
    PhaseCellInterface.ErrorOn active
      (pairedCellRead p (2*p+13)
        (cstream A (2*p+13) (chirpLine s (fun i => finalRoundWord w q p j (G i)))))
      (fun i => ((2 : ℂ)^j)⁻¹*x i) (2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^j) := by
  intro i hi
  have hmag := inverse_round_magnitude p target _ _ (hx i hi) (he i hi)
  have hd := roundBatchField_decoded (j := j) (E := p+8) hA hw hp G [] i hmag
  have hwidth : p+(p+8)+5 = 2*p+13 := by omega
  simp only [List.append_nil,hwidth] at hd
  rw [hd]
  exact scaleRound_error p j _ _ _ (he i hi)

theorem normalizedBatch_accuracy {A w q p j target : ℕ} (hA : 4 ≤ A) (hw : 1 ≤ w)
    (hpq : p ≤ q) (hp : 0 < p) (M : Matrix (ZMod s) (ZMod s) ℝ) (active : Finset (ZMod s))
    (hM : DominatesOn M active (1/(8*(p : ℝ))))
    (Fs Gs : List (ZMod s → GaussianInt))
    (x y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hF : ∀ F ∈ Fs, ∀ i, ‖value q (F i)‖ ≤ (2 : ℝ)^2)
    (hx : ∀ F ∈ Fs, Solves M active (x F) (fun i => (value q (F i)).re))
    (hy : ∀ F ∈ Fs, Solves M active (y F) (fun i => (value q (F i)).im))
    (he : List.Forall₂ (fun F G => PhaseCellInterface.ErrorOn active
      (pairedCellRead q w (cstream A w (chirpLine s G)))
      (fun i => (⟨x F i,y F i⟩ : ℂ)) (1/(2 : ℝ)^target)) Fs Gs) :
    List.Forall₂ (fun F H => PhaseCellInterface.ErrorOn active
      (pairedCellRead p (2*p+13) (cstream A (2*p+13) (chirpLine s H)))
      (fun i => ((2 : ℂ)^j)⁻¹*(⟨x F i,y F i⟩ : ℂ))
      (2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^j))
      Fs (Gs.map (fun G i => finalRoundWord w q p j (G i))) := by
  have hnorm : ∀ F ∈ Fs, ∀ i ∈ active, ‖(⟨x F i,y F i⟩ : ℂ)‖ ≤ 64*(p : ℝ) := by
    intro F hmem i hi
    have h := dominant_complex_solution_bound M active p 2 hp hM
      (fun i => (⟨x F i,y F i⟩ : ℂ)) (fun i => value q (F i)) (hx F hmem) (hy F hmem)
      (fun i _ => hF F hmem i) i hi
    norm_num at h
    nlinarith only [h]
  have hwith := (List.forall₂_and_left Fs Gs).mpr ⟨hnorm,he⟩
  apply List.forall₂_map_right_iff.mpr
  exact hwith.imp (fun F G h => roundedField_accuracy hA hw hpq active G _ h.1 h.2)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
