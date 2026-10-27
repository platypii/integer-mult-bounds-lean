module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNegativeUnitField
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealCouplingField
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBorrowedCouplingPassSpec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundedAmbient
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupportBudget
public import IntegerMultBounds.NLogN.PhaseCellCouplingMass

/-! The executed boundary coupling pass produces original-matrix columns, including all aliases. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem originalColumn_real {s : ℕ} [NeZero s] (P q t u band a b : ℕ) (j i : ZMod s) :
    (couplingRowField P q t u band a b true (negativeUnitField q j) (fun _ => 0) i).im = 0 := by
  have hn (k : ZMod s) : realPartWord (negativeUnitField q j k) = negativeUnitField q j k := by
    ext <;> simp [realPartWord,negativeUnitField_real]
  have hz : realPartWord (0 : GaussianInt) = 0 := rfl
  have hh := couplingRowField_realPart P q t u band a b true (negativeUnitField q j) (fun _ => 0) i
  have hp : realPartWord (couplingRowField P q t u band a b true (negativeUnitField q j) (fun _ => 0) i) =
      couplingRowField P q t u band a b true (negativeUnitField q j) (fun _ => 0) i := by
    simpa only [hn,hz] using hh
  exact (congrArg (fun z : GaussianInt => z.im) hp).symm

theorem originalColumnPass_spec (hQ : SS.states ≤ Q)
    {p q w s t u a b : ℕ} [NeZero s] {α d : ℝ}
    (hA : 96 ≤ A) (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t)
    (hαu : α^2 = (u : ℝ)) (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hw : q+couplingRowExponent 0 0 (8*p+1) (couplingCountExponent p u)+2 ≤ w)
    (haS : a ≤ s) (hbS : b ≤ s) (hbandS : PhaseCellBand.width p u ≤ s)
    (j : ZMod s) (hj : j ∈ haloBoundary s t (PhaseCellBand.width p u) a b)
    (tail sourceTail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady (2^15*p) q w s t u (PhaseCellBand.width p u) a b
      (cstream A w (chirpLine s (fun _ => 0))++tail) (embStk groupReg S))
    (hindex : S.R 107 = [])
    (hsource : S.R 132 = cstream A w (chirpLine s (negativeUnitField q j))++sourceTail)
    (h143 : S.R 143 = []) (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = []) :
    let band := PhaseCellBand.width p u
    let column := couplingRowField (2^15*p) q t u band a b true (negativeUnitField q j) (fun _ => 0)
    let output := cstream A w (chirpLine s column)++S.R 113
    ∃ v' m, v'.user = v.user ∧ m ≤ borrowedCouplingPassCost true (2^15*p) q w s t u band a b ∧
      Exec (embTab groupReg body) (borrowedCouplingPass hQ true) (mk v S) m
        (mk v' {S with R := Function.update S.R 113 output}) ∧
      (∀ i, ‖value q (column i)‖ ≤ (2 : ℝ)^couplingRowExponent 0 0 (8*p+1) (couplingCountExponent p u)) ∧
      (∀ i, (column i).im = 0) ∧
      (∀ i, ‖value q (column i)‖ ≤ 2+3*(2*band+1)*(1/(2 : ℝ)^q)) ∧
      ∀ i, |publishedCellRead q w (0 : ZMod s) output i-realMatrix s t p u i j| ≤
        3*(2*band+1)*(1/(2 : ℝ)^q) := by
  dsimp only
  let band := PhaseCellBand.width p u
  let column := couplingRowField (2^15*p) q t u band a b true (negativeUnitField q j) (fun _ => 0)
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hθpos : 0 < (t : ℝ)/s-1 := lt_of_lt_of_le (by positivity) hθ
  obtain ⟨v',m,hu,hm,he,hfield,hlen,hnorm,herror⟩ := borrowedCouplingPass_spec (body := body)
    (rhsExp := 0) (inputExp := 0) (countExp := couplingCountExponent p u)
    hQ true hA (by omega) hst hαu hθpos hgap hbudget hw haS hbS hbandS rfl
    (negativeUnitField q j) (fun _ => 0) (fun k => (value q (negativeUnitField q j k)).re) (fun _ => 0)
    2 0 0 (by norm_num) (couplingCountExponent_spec p u)
    (by
      intro k
      have hz : value q (0 : GaussianInt) = 0 := by apply Complex.ext <;> simp [value]
      rw [hz]
      norm_num)
    (by intro k _; simpa only [pow_zero] using negativeUnitField_norm q j k)
    (by intro k _; simp)
    (couplingOffsets_mass_le_two hst hα p u hp hwidth hαu hθ hgap hbudget)
    (by intro k; simp [value]) tail sourceTail v S hready hindex hsource h143 h131 h134 h135
  have hsame : guardedCouplingRowField (2^15*p) q t u band a b true
      (negativeUnitField q j) (fun _ => 0) = couplingRowField (2^15*p) q t u band a b true
      (negativeUnitField q j) (fun _ => 0) := by
    funext i
    exact guardedCouplingRowField_eq hst (2^15*p) q u band a b true hbS _ _ i (Or.inl rfl)
  rw [hsame] at hfield hnorm
  have hfit (i : ZMod s) : Fits w (column i) := fits_of_value_power hw _ (hnorm i)
  have hw0 : 0 < w := by omega
  have haccuracy (i : ZMod s) : |(value q (column i)).re-realMatrix s t p u i j| ≤
      3*(2*band+1)*(1/(2 : ℝ)^q) := by
    have hh := herror i.val i.val_lt (Or.inl rfl)
    rw [hfield,cstream_word w (chirpLine s column) (S.R 113) i.val (by simpa using i.val_lt)] at hh
    simp only [chirpLine,List.getElem_map,List.getElem_range,ZMod.natCast_zmod_val] at hh
    rw [decodeWord_of_fits (by omega) hw0 _ (hfit i)] at hh
    have hcol := couple_negative_unit (realMatrix s t p u) (haloBoundary s t band a b) q j hj i
    have hh' : |(value q (column i)).re-realMatrix s t p u i j| ≤
        (2*band+1)*(2/(2 : ℝ)^q)+(2*band+1)*(1/(2 : ℝ)^q) := by
      change |(value q (column i)).re-(0-SchurDominance.couple (realMatrix s t p u)
        (haloBoundary s t band a b) (fun k => (value q (negativeUnitField q j k)).re) i)| ≤
        (2*band+1)*(2/(2 : ℝ)^q)+0+(2*band+1)*((2 : ℝ)^0*(1/(2 : ℝ)^q))+2*0 at hh
      rw [zero_sub,hcol] at hh
      simpa only [pow_zero,one_mul,add_zero,mul_zero] using hh
    exact hh'.trans_eq (by ring)
  have hreal (i : ZMod s) : (column i).im = 0 := originalColumn_real _ _ _ _ _ _ _ _ _
  have hnorm' (i : ZMod s) : ‖value q (column i)‖ ≤ 2+3*(2*band+1)*(1/(2 : ℝ)^q) := by
    let : NeZero t := ⟨by omega⟩
    have hentry : |realMatrix s t p u i j| ≤ 2 := by
      apply (Finset.single_le_sum (fun k _ => abs_nonneg (realMatrix s t p u i k)) (Finset.mem_univ j)).trans
      have hsum := matrix_row_sum_le_two hst hα p u hp hwidth hαu hθ hgap hbudget i
      have hn (k : ZMod s) : 0 ≤ realMatrix s t p u i k := by
        unfold realMatrix
        exact_mod_cast matrix_nonneg s t p u i k
      simpa only [abs_of_nonneg (hn _)] using hsum
    have hproj : realPartWord (column i) = column i := by
      ext <;> simp [realPartWord,hreal i]
    have hv : ‖value q (column i)‖ = |(value q (column i)).re| := by
      simpa only [hproj] using value_realPartWord_norm q (column i)
    rw [hv]
    calc
      _ = |((value q (column i)).re-realMatrix s t p u i j)+realMatrix s t p u i j| := by congr 1; ring
      _ ≤ |(value q (column i)).re-realMatrix s t p u i j|+|realMatrix s t p u i j| := abs_add_le _ _
      _ ≤ _ := by linarith [haccuracy i]
  refine ⟨v',m,hu,hm,by simpa only [hfield] using he,hnorm,hreal,hnorm',?_⟩
  intro i
  rw [publishedCellRead_encodedField (by omega) hw0 column (S.R 113) hfit i]
  exact haccuracy i

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
