module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleasedSchurResidual
public import IntegerMultBounds.NLogN.PhaseCellHaloSchurColumns
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitialErrorBudget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComponentWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundedAmbient
public import IntegerMultBounds.NLogN.PhaseCellHaloSchurStability

/-! The executed residual pass supplies physical Schur-column entries with charged input error. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem releasedSchurColumn_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (B : ZMod s → GaussianInt)
    (hB : ∀ i, ‖value (executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp) (B i)‖ ≤ (2 : ℝ)^rhsExp)
    (v : HS 148 Q A U) (S : Stacks 148 A) (tail : List (Fin (A+4)))
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = [])
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1)
      (executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp) (chirpLine s B)++tail) (embStk componentReg S)) (h147 : S.R 147 = [])
    (j : ZMod s) (hj : j ∈ haloBoundary s t (PhaseCellBand.width p u) a b)
    (η : ℝ) (hη : 0 ≤ η)
    (hcolumn : ∀ k ∈ haloVertices s a b,
      |(value (executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp) (B k)).re-
        realMatrix s t p u k j| ≤ η) :
    let q := executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp
    let w := executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp
    let band := PhaseCellBand.width p u
    let I := haloInterior s t band a b
    let boundary := haloBoundary s t band a b
    ∃ v' n, ∃ D : ZMod s → GaussianInt, ∃ R : (ZMod s → ℝ) → ZMod s → ℝ,
      let C := couplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (B i))
      let input := cstream A w (chirpLine s C)++S.R 110
      let S' : Stacks 148 A := {S with R := Function.update S.R 110 input}
      (∀ c, SchurDominance.Solves (realMatrix s t p u) I (R c) c) ∧
      v'.user = v.user ∧ n ≤ releasedSchurResidualCost p l s t u target rhsExp a b ∧
      Exec (embTab componentReg (embTab groupReg body)) (releasedSchurResidual hR hQ) (mk v S) n (mk v' S') ∧
      (∀ i, (C i).im = 0) ∧
      (∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp)
        (8*p+1) (couplingCountExponent p u)) ∧
      (∀ i ∈ boundary, 8*p*|(value q (C i)).re-SchurDominance.residual (realMatrix s t p u) I R
          (fun i => (value q (B i)).re) i| ≤ 1/(2 : ℝ)^(recoveryTarget p target+2)) ∧
      (∀ i ∈ boundary,
        |publishedCellRead q w (0 : ZMod s) (S'.R 110) i-
          (SchurDominance.run (realMatrix s t p u) (haloVertices s a b) I.toList).1 i j| ≤
          (1/(2 : ℝ)^(recoveryTarget p target+2))/(8*(p : ℝ))+(1+16*(p : ℝ))*η) ∧
      (∀ i, publishedCellRead q w (0 : ZMod s) (S'.R 110) i = (value q (C i)).re) ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1) q l s t u band 0 0 input
        (embStk componentReg S') := by
  dsimp only
  let firstTarget := initialSchurTarget p u target rhsExp
  let q := executionPrecision p l firstTarget rhsExp
  let w := executionWidth p l firstTarget rhsExp
  let band := PhaseCellBand.width p u
  let I := haloInterior s t band a b
  let E := (1/(2 : ℝ)^(recoveryTarget p target+2))/(8*(p : ℝ))
  obtain ⟨v',n,D,R,hRsolve,hu',hn,he,hCreal,hCnorm,hCerror,hread,hready'⟩ := releasedSchurResidual_spec (body := body)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad B hB v S tail
    h127 h138 h143 haMaster hbMaster hready h147
  let C := couplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (B i))
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hres : ∀ i ∈ haloBoundary s t band a b,
      |(value q (C i)).re-SchurDominance.residual (realMatrix s t p u) I R
        (fun k => (value q (B k)).re) i| ≤ E := by
    intro i hi
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8*(p : ℝ))).mpr
    have hh : 8*(p : ℝ)*|(value q (C i)).re-SchurDominance.residual (realMatrix s t p u) I R
        (fun k => (value q (B k)).re) i| ≤ 1/(2 : ℝ)^(recoveryTarget p target+2) := hCerror i hi
    simpa only [mul_comm] using hh
  have hentry := halo_schur_column_error hst hα p u a b hp hwidth hαu hθ hgap hbudget R hRsolve j hj
    (fun k => (value q (B k)).re) (fun k => (value q (C k)).re) η E hη hcolumn hres
  refine ⟨v',n,D,R,hRsolve,hu',hn,he,hCreal,hCnorm,hCerror,?_,hread,hready'⟩
  intro i hi
  rw [hread i]
  exact hentry i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
