module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealInputWord
public import IntegerMultBounds.MathlibTM2.Mult.ChirpScaleExec
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputBounds
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairComponentsAccuracy

/-! A grid input halved at solver precision is an exact numerator shift. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Machine
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ChirpSt
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem realInputWord_half_grid (p d : ℕ) (z : ℤ) :
    realInputWord (p+1+d) ((1/2 : ℝ)*((z : ℝ)/(2 : ℝ)^p)) =
      ⟨z*(2 : ℤ)^d,0⟩ := by
  have he : (1/2 : ℝ)*((z : ℝ)/(2 : ℝ)^p) =
      ((z*(2 : ℤ)^d : ℤ) : ℝ)/(2 : ℝ)^(p+1+d) := by
    push_cast
    rw [pow_add,pow_add,pow_one]
    field_simp
  rw [he,realInputWord_grid]

/-- Convert a borrowed complex grid line to the solver's half-sized RHS exactly. -/
theorem halfGrid_value (p d : ℕ) (z : GaussianInt) :
    value (p+1+d) ((2 : GaussianInt)^d*z) = (1/2 : ℂ)*value p z := by
  rw [value_pow_two_mul,value_eq_grid,value_eq_grid,pow_add,pow_add,pow_one]
  field_simp

/-- Five guard bits suffice for every converted input of norm at most one. -/
theorem halfGrid_fits (p d w : ℕ) (hw : p+1+d+5 ≤ w) (z : GaussianInt)
    (hz : ‖value p z‖ ≤ 1) : Fits w ((2 : GaussianInt)^d*z) := by
  apply fits_chirpOutput_bound (p+1+d) 0 0 w _ _ (by simpa using hw)
  rw [halfGrid_value,norm_mul]
  have hn : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by norm_num
  rw [hn]
  norm_num
  linarith

/-- Converted tape words decode to the half-sized input, without a fit premise. -/
theorem halfGrid_decoded {A s : ℕ} [NeZero s] (hA : 4 ≤ A)
    (p d w : ℕ) (hw : p+1+d+5 ≤ w) (F : ZMod s → GaussianInt)
    (hF : ∀ i, ‖value p (F i)‖ ≤ 1) (tail : List (Fin (A+4))) (i : ZMod s) :
    pairedCellRead (p+1+d) w
      (cstream A w (chirpLine s (fun k => (2 : GaussianInt)^d*F k))++tail) i =
      (1/2 : ℂ)*value p (F i) := by
  have hf := halfGrid_fits p d w hw (F i) (hF i)
  have hr := pairedCellRead_encodedField (q := p+1+d) hA (show 0 < w by omega)
    (fun k => (2 : GaussianInt)^d*F k) tail i hf
  exact hr.trans (halfGrid_value p d (F i))

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- The same execution witness carries the exact half-grid input semantics. -/
theorem halfGrid_exec {src buf shift rest savedShift savedRest : Fin T}
    (hreg : [src,buf,shift,rest,savedShift,savedRest].Nodup)
    (w p d : ℕ) (hw : 1 ≤ w) (hd : d ≤ w) (xs : List GaussianInt)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R src = cstream A w xs)
    (hshift : (S.R shift).length = d) (hrest : (S.R rest).length = w-d)
    (hbuf : S.R buf = []) (hsavedShift : S.R savedShift = [])
    (hsavedRest : S.R savedRest = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (shiftInto src buf src shift rest savedShift savedRest (pairSym A false false))
        (mk v S) (xs.length*(6*w+4*d+14)+4)
        (mk v' {S with R := (Function.update S.R src
          (cstream A w (xs.map fun z => (2 : GaussianInt)^d*z)))}) ∧
      ∀ z ∈ xs, value (p+1+d) ((2 : GaussianInt)^d*z) = (1/2 : ℂ)*value p z := by
  obtain ⟨v',hu,he⟩ := chirpScale_exec (body := body) hreg w d hw hd xs v S
    hsrc hshift hrest hbuf hsavedShift hsavedRest
  exact ⟨v',hu,he,fun z _ => halfGrid_value p d z⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
