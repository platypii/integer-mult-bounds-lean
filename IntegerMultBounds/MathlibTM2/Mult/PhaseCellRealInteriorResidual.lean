module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoredInteriorResidual
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealResidualProjection
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellResidualSizing
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGuardedCouplingField
public import IntegerMultBounds.NLogN.PhaseCellCouplingMass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupportBudget

/-! Real interior/residual output with precision-independent magnitudes and paid projection. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def realInteriorResidual (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  .seq (restoredInteriorResidual hR hQ) realResidualProjection

def realInteriorResidualCost (p l s t u target rhsExp a b : ℕ) : ℕ :=
  restoredInteriorResidualCost p l s t u target rhsExp a b+
    realResidualProjectionCost (executionPrecision p l target rhsExp) s

theorem realInteriorResidual_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l s t p u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re))
    (v : HS 144 Q A U) (S : Stacks 144 A) (borrowed : List (Fin (A+4)))
    (h127 : S.R 127 = []) (h138 : S.R 138 = [])
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l target rhsExp) (chirpLine s C)++borrowed) S)
    (h143 : S.R 143 = []) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let band := PhaseCellBand.width p u
    let e := stableInteriorExponent p rhsExp
    ∃ v' n, ∃ D : ZMod s → GaussianInt,
      let R := guardedCouplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (C i))
      v'.user = v.user ∧ n ≤ realInteriorResidualCost p l s t u target rhsExp a b ∧
      Exec (embTab groupReg body) (realInteriorResidual hR hQ) (mk v S) n
        (mk v' {S with R := (Function.update
          (Function.update S.R 132 (cstream A w (chirpLine s D)++S.R 132))
          110 (cstream A w (chirpLine s R)++S.R 110))}) ∧
      (∀ i, (D i).im = 0) ∧
      (∀ i ∈ haloInterior s t band a b, ‖value q (D i)‖ ≤ (2 : ℝ)^e) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t band a b)
        (fun i => (value q (D i)).re) x (1/(2 : ℝ)^target) ∧
      (∀ i, (R i).im = 0) ∧
      (∀ i, ‖value q (R i)‖ ≤ (2 : ℝ)^couplingRowExponent rhsExp e (8*p+1) (couplingCountExponent p u)) ∧
      ∀ i ∈ haloBoundary s t band a b, |(value q (R i)).re-((value q (C i)).re-
        SchurDominance.couple (realMatrix s t p u) (haloInterior s t band a b) x i)| ≤
          (2*band+1)*(2/(2 : ℝ)^q)+(2*band+1)*((2 : ℝ)^e*(1/(2 : ℝ)^q))+2*(1/(2 : ℝ)^target) := by
  dsimp only
  let countExp := couplingCountExponent p u
  have hcount := couplingCountExponent_spec p u
  have hcountBudget := couplingCountExponent_le_execution p u l target rhsExp
  have hmass := couplingOffsets_mass_le_two hst hα p u hp hwidth hαu hθ hgap hbudget
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let band := PhaseCellBand.width p u
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hθ0 : 0 < (t : ℝ)/s-1 := lt_of_lt_of_le (by positivity) hθ
  let : NeZero t := ⟨by omega⟩
  have hrowWidth := interiorResidual_width hcountBudget
  have hdom := matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget
  obtain ⟨v₁,n₁,D,hu₁,hn₁,he₁,hDnorm,hDerror,hRnorm,hRerror⟩ := restoredInteriorResidual_spec
    (body := body) hR hQ hA hp0 hst hu hαu hθ0 hgap hbudget hband has hbs hpad C hC x hx
    v S borrowed h127 h138 haMaster hbMaster hready h143 hcount hrowWidth 2 hmass
  let R := guardedCouplingRowField (2^15*p) q t u band a b false D C
  let S₁ : Stacks 144 A := {S with R := (Function.update
    (Function.update S.R 132 (cstream A w (chirpLine s D)++S.R 132))
    110 (cstream A w (chirpLine s R)++S.R 110))}
  have hw : 2*q+8 = w := by dsimp [q,w,executionPrecision,executionWidth]; omega
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := realResidualProjection_exec (body := embTab groupReg body)
    (by omega) q s (chirpLine s D) (chirpLine s R) (S.R 132) (S.R 110) (by simp) (by simp) v₁ S₁
    (by simpa [S₁,groupHeaderValue,q] using hready.masters (119,112) (by simp [groupHeaderCopies]))
    (by simpa [S₁,groupHeaderValue] using hready.masters (121,97) (by simp [groupHeaderCopies]))
    (by simp [S₁,hw]) (by simp [S₁,hw])
    (by simpa [S₁] using hready.blank 94 (by decide) (by decide) (by decide))
    (by simpa [S₁] using hready.fresh 131 (by simp))
    (by simpa [S₁] using hready.fresh 134 (by simp))
    (by simpa [S₁] using hready.fresh 135 (by simp))
  let D' := fun i => realPartWord (D i)
  let C' := fun i => realPartWord (C i)
  have hD' : ∀ i ∈ haloInterior s t band a b,
      ‖value q (D' i)‖ ≤ (2 : ℝ)^stableInteriorExponent p rhsExp :=
    stableInterior_norm hp0 _ hdom C D hC x hx hDerror
  have hR' : ∀ i, ‖value q (guardedCouplingRowField (2^15*p) q t u band a b false D' C' i)‖ ≤
      (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp) (8*p+1) countExp :=
    guardedCouplingRowField_norm false hp0 hst hαu hθ0 hgap hbudget D' C' hcount
      (fun i => by
        rw [value_realPartWord_norm]
        exact (Complex.abs_re_le_norm _).trans (hC i)) hD'
  refine ⟨v₂,n₁+n₂,D',hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,
    (Exec.seq he₁ he₂).cast rfl ?_,fun i => rfl,hD',?_,?_,hR',?_⟩
  · apply congrArg (mk v₂)
    simp only [hw]
    have hDline : (chirpLine s D).map realPartWord = chirpLine s D' := by
      simp [chirpLine,D',List.map_map,Function.comp_def]
    have hRline : (chirpLine s R).map realPartWord =
        chirpLine s (guardedCouplingRowField (2^15*p) q t u band a b false D' C') := by
      simp [chirpLine,R,D',C',List.map_map,Function.comp_def,guardedCouplingRowField_realPart]
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk110 : k = 110 <;> by_cases hk132 : k = 132 <;>
      simp [S₁,hDline,hRline,hk110,hk132,q,w,band,C']
  · simpa only [D',value_realPartWord_re] using hDerror
  · intro i
    rw [← guardedCouplingRowField_realPart]
    rfl
  · intro i hi
    have hsharpWidth : q+couplingRowExponent rhsExp (stableInteriorExponent p rhsExp)
        (8*p+1) countExp+2 ≤ w := stableInteriorResidual_width p u l target rhsExp
    have hC' (i) : ‖value q (C' i)‖ ≤ (2 : ℝ)^rhsExp := by
      rw [value_realPartWord_norm]
      exact (Complex.abs_re_le_norm _).trans (hC i)
    have hpoint := guardedCouplingRowField_error (A := A) (w := w) (rhsExp := rhsExp)
      (inputExp := stableInteriorExponent p rhsExp) (countExp := countExp) false hA
      hp0 hst hαu hθ0 hgap hbudget hsharpWidth D' C' x (fun i => (value q (C i)).re)
      2 (1/(2 : ℝ)^target) 0 (by positivity) hcount hC' hD'
      (by intro j hj; simpa only [D',value_realPartWord_re,Real.norm_eq_abs] using hDerror j hj)
      hmass (by intro j; simp [C']) hbs i (Or.inr hi)
    simpa only [Bool.false_eq_true,ite_false,add_zero] using hpoint

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
