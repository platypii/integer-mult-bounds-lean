module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedSchurColumn
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryWorkspace

/-! Generate a Schur column while the prepared folded page remains resident. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def boundarySchurColumn (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 151 Q A U :=
  embProg boundaryArithmeticReg id (generatedSchurColumn hR hQ)

theorem boundarySchurColumn_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (j : ZMod s) (hj : j ∈ haloBoundary s t (PhaseCellBand.width p u) a b)
    (v : HS 151 Q A U) (S : Stacks 151 A) (tail : List (Fin (A+4)))
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u target 2) 2) l s t u (PhaseCellBand.width p u) 0 0 tail (embStk componentReg (embStk boundaryArithmeticReg S)))
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hcoordinate : (S.R 139).length = j.val)
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = []) (h147 : S.R 147 = []) :
    let q := executionPrecision p l (initialSchurTarget p u target 2) 2
    let w := executionWidth p l (initialSchurTarget p u target 2) 2
    let band := PhaseCellBand.width p u
    let B := couplingRowField (2^15*p) q t u band a b true (negativeUnitField q j) (fun _ => 0)
    ∃ v' m, ∃ D : ZMod s → GaussianInt,
      let C := couplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (B i))
      let output := cstream A w (chirpLine s C)++tail
      let S' : Stacks 151 A := {S with R := Function.update S.R 110 output}
      v'.user = v.user ∧ m ≤ generatedSchurColumnCost p u l s t a b target j.val ∧
      Exec (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))) (boundarySchurColumn hR hQ) (mk v S) m (mk v' S') ∧
      (∀ i, (C i).im = 0) ∧
      (∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2)
        (8*p+1) (couplingCountExponent p u)) ∧
      (∀ i ∈ haloBoundary s t band a b,
        |publishedCellRead q w (0 : ZMod s) (S'.R 110) i-
          (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
            (haloInterior s t band a b).toList).1 i j| ≤ 1/(2 : ℝ)^target) ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
        q l s t u band 0 0 output (embStk componentReg (embStk boundaryArithmeticReg S')) := by
  dsimp only
  obtain ⟨v₁,m,D,hu₁,hm,he,hreal,hnorm,herror,hready₁⟩ := generatedSchurColumn_spec (body := body)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad j hj
    (embDn boundaryArithmeticReg v) (embStk boundaryArithmeticReg S) tail hready
    (by simpa [embStk,boundaryArithmeticReg] using haMaster)
    (by simpa [embStk,boundaryArithmeticReg] using hbMaster)
    (by simpa [embStk,boundaryArithmeticReg] using hcoordinate)
    (by simpa [embStk,boundaryArithmeticReg] using h127)
    (by simpa [embStk,boundaryArithmeticReg] using h138)
    (by simpa [embStk,boundaryArithmeticReg] using h143)
    (by simpa [embStk,boundaryArithmeticReg] using h147)
  obtain ⟨v₂,hu₂,he₂⟩ := boundaryArithmeticExec_source (generatedSchurColumn hR hQ) v S v₁ m _ hu₁ he
  refine ⟨v₂,m,D,hu₂,hm,he₂,hreal,hnorm,?_,?_⟩
  · simpa [embStk,boundaryArithmeticReg] using herror
  · rw [boundaryArithmeticProject_source]
    exact hready₁

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
