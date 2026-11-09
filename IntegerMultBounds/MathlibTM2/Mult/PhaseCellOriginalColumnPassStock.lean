module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNegativeUnitField
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealCouplingField
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBorrowedCouplingPassSpecStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginalColumnPass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundedAmbient
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupportBudget
public import IntegerMultBounds.NLogN.PhaseCellCouplingMass

/-! The executed boundary coupling pass produces original-matrix columns, including all aliases. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem originalColumnPass_spec_within (hQ : SS.states ≤ Q)
    {p q w s t u a b : ℕ} [NeZero s] {α d : ℝ}
    (hA : 96 ≤ A) (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t)
    (hαu : α^2 = (u : ℝ)) (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hw : q+couplingRowExponent 0 0 (8*p+1) (couplingCountExponent p u)+2 ≤ w)
    (haS : a ≤ s) (hbS : b ≤ s) (hbandS : PhaseCellBand.width p u ≤ s)
    (j : ZMod s) (hj : j ∈ haloBoundary s t (PhaseCellBand.width p u) a b)
    (tail sourceTail : List (Fin (A+4))) (R : ℕ) (hpush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ R)
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady (2^15*p) q w s t u (PhaseCellBand.width p u) a b
      (cstream A w (chirpLine s (fun _ => 0))++tail) (embStk groupReg S))
    (hindex : S.R 107 = [])
    (hsource : S.R 132 = cstream A w (chirpLine s (negativeUnitField q j))++sourceTail)
    (h143 : S.R 143 = []) (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = []) :
    let band := PhaseCellBand.width p u
    let column := couplingRowField (2^15*p) q t u band a b true (negativeUnitField q j) (fun _ => 0)
    let output := cstream A w (chirpLine s column)++S.R 113
    ∃ v' m, v'.user = v.user ∧ m ≤ borrowedCouplingPassCost true (2^15*p) q w s t u band a b ∧
      ExecWithin (embTab groupReg body) (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
        borrowedCouplingPassWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U) true R (2^15*p) q w s t u band a b) 0
        (borrowedCouplingPass hQ true) (mk v S) m
        (mk v' {S with R := Function.update S.R 113 output}) ∧
      (∀ i, ‖value q (column i)‖ ≤ (2 : ℝ)^couplingRowExponent 0 0 (8*p+1) (couplingCountExponent p u)) ∧
      (∀ i, (column i).im = 0) ∧
      (∀ i, ‖value q (column i)‖ ≤ 2+3*(2*band+1)*(1/(2 : ℝ)^q)) ∧
      ∀ i, |publishedCellRead q w (0 : ZMod s) output i-realMatrix s t p u i j| ≤
        3*(2*band+1)*(1/(2 : ℝ)^q) := by
  dsimp only
  let band := PhaseCellBand.width p u
  let column := couplingRowField (2^15*p) q t u band a b true (negativeUnitField q j) (fun _ => 0)
  obtain ⟨vOld,mOld,huOld,hmOld,heOld,hpost⟩ := originalColumnPass_spec (body := body)
    hQ hA hp hwidth hα hst hαu hθ hgap hbudget hw haS hbS hbandS j hj
    tail sourceTail v S hready hindex hsource h143 h131 h134 h135
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hθpos : 0 < (t : ℝ)/s-1 := lt_of_lt_of_le (by positivity) hθ
  obtain ⟨v',m,hu,hm,he,hfield,hlen,hnorm,herror⟩ := borrowedCouplingPass_spec_within (body := body)
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
    (by intro k; simp [value]) tail sourceTail R hpush v S hready hindex hsource h143 h131 h134 h135
  have hsame : guardedCouplingRowField (2^15*p) q t u band a b true
      (negativeUnitField q j) (fun _ => 0) = couplingRowField (2^15*p) q t u band a b true
      (negativeUnitField q j) (fun _ => 0) := by
    funext i
    exact guardedCouplingRowField_eq hst (2^15*p) q u band a b true hbS _ _ i (Or.inl rfl)
  rw [hsame] at hfield
  have heColumn : ExecWithin (embTab groupReg body) (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
      borrowedCouplingPassWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U) true R (2^15*p) q w s t u band a b) 0
      (borrowedCouplingPass hQ true) (mk v S) m
      (mk v' {S with R := Function.update S.R 113 (cstream A w (chirpLine s column)++S.R 113)}) := by
    simpa only [hfield] using he
  obtain ⟨hmEq,hEq⟩ := heColumn.toExec.unique heOld
  rw [hmEq,hEq] at heColumn
  exact ⟨vOld,mOld,huOld,hmOld,heColumn,hpost⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
