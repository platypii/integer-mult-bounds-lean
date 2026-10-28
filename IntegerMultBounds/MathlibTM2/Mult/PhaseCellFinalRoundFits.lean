module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFinalRoundRuns

/-! Derive final signed output fits from the numerical solver's magnitude bound. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor

theorem value_finalRound (q p j : ℕ) (hp : p ≤ q) (z : GaussianInt) :
    value p (tdivN (q-p+j) z) = rhoC p (((2 : ℂ)^j)⁻¹*value q z) := by
  have he : value q z = (⟨gv q z.re,gv q z.im⟩ : ℂ) := rfl
  rw [he,rhoC_scale q p j hp]
  apply Complex.ext <;> simp only [value,rsbGrid,two_pow_complex,toComplex_div_re,toComplex_div_im]

theorem finalRound_fits (q p j E k : ℕ) (hp : p ≤ q) (hk : p+E+5 ≤ k)
    (z : GaussianInt) (hz : ‖value q z‖ ≤ 8*(2 : ℝ)^E) :
    Fits k (tdivN (q-p+j) z) := by
  apply fits_chirpOutput_bound p E 0 k _ _ (by simpa using hk)
  rw [value_finalRound q p j hp]
  have hscale : ‖((2 : ℂ)^j)⁻¹‖ ≤ 1 := by
    rw [norm_inv,norm_pow,Complex.norm_ofNat]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  calc
    _ ≤ ‖((2 : ℂ)^j)⁻¹*value q z‖ := norm_rhoC_le p _
    _ = ‖((2 : ℂ)^j)⁻¹‖*‖value q z‖ := norm_mul _ _
    _ ≤ 1*‖value q z‖ := mul_le_mul_of_nonneg_right hscale (norm_nonneg _)
    _ ≤ 8*(2 : ℝ)^(E+0) := by simpa using hz

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

/-- One witness gives execution, restoration and the normalized decoded output. -/
theorem finalRound_field_exec (hA : 4 ≤ A) {src dst tmp cW cS cE cD sp sg cy : Fin T}
    (hreg : [src,dst,tmp,cW,cS,cE,cD,sp,sg,cy].Nodup)
    (w q p j E k : ℕ) (hp : p ≤ q) (hw : q+E+5 ≤ w)
    (hk : p+E+5 ≤ k) (hsize : q-p+j+k ≤ w)
    (G : ZMod s → GaussianInt) (hG : ∀ i, ‖value q (G i)‖ ≤ 8*(2 : ℝ)^E)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = cstream A w (chirpLine s G)) (hdst : S.R dst = [])
    (hg : topShiftG tmp cW cS cE cD sp sg cy w (q-p+j) k S.R) :
    ∃ v', v'.user = v.user ∧
      Exec body (topPass src dst (topShiftWord src dst tmp cW cS cE cD sp sg cy))
        (mk v S) (1+(s*(topShiftWordCost w (q-p+j) k+1)+1)+(2*(s*k)+2))
        (mk v' {S with R := (Function.update S.R src
          (cstream A k (chirpLine s (fun i => tdivN (q-p+j) (G i)))))}) ∧
      ∀ i, pairedCellRead p k
        (cstream A k (chirpLine s (fun i => tdivN (q-p+j) (G i)))) i =
        rhoC p (((2 : ℂ)^j)⁻¹*value q (G i)) := by
  have hfit : ∀ z ∈ chirpLine s G, Fits w z := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hz
    exact fits_chirpOutput_bound q E 0 w _ (by simpa using hG (i : ZMod s)) (by simpa using hw)
  obtain ⟨v',hu,he⟩ := finalRound_runs (body := body) hA hreg w q p j k (by omega)
    hsize (chirpLine s G) hfit v S hsrc hdst hg
  have hmap : (chirpLine s G).map (tdivN (q-p+j)) =
      chirpLine s (fun i => tdivN (q-p+j) (G i)) := by simp only [chirpLine,List.map_map,Function.comp_def]
  rw [hmap] at he
  refine ⟨v',hu,?_,?_⟩
  · simpa only [chirpLine,List.length_map,List.length_range] using he
  · intro i
    have hd := pairedCellRead_encodedField (q := p) hA (show 0 < k by omega)
      (fun i => tdivN (q-p+j) (G i)) [] i (finalRound_fits q p j E k hp hk (G i) (hG i))
    simpa only [List.append_nil] using hd.trans (value_finalRound q p j hp (G i))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
