module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealInteriorResidual
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComponentWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundedAmbient
public import IntegerMultBounds.NLogN.PhaseCellHaloSchurStability

/-! Execute the retained initial pass and produce the Schur RHS contract from its actual words. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def retainedSchurResidual (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 148 Q A U :=
  embProg componentReg id (realInteriorResidual hR hQ)

theorem retainedSchurResidual_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (B : ZMod s → GaussianInt)
    (hB : ∀ i, ‖value (executionPrecision p l target rhsExp) (B i)‖ ≤ (2 : ℝ)^rhsExp)
    (v : HS 148 Q A U) (S : Stacks 148 A) (tail : List (Fin (A+4)))
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = [])
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l target rhsExp) (chirpLine s B)++tail) (embStk componentReg S)) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let band := PhaseCellBand.width p u
    let I := haloInterior s t band a b
    let boundary := haloBoundary s t band a b
    ∃ v' n, ∃ D : ZMod s → GaussianInt, ∃ R : (ZMod s → ℝ) → ZMod s → ℝ,
      let C := couplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (B i))
      let input := cstream A w (chirpLine s C)++S.R 110
      let output := cstream A w (chirpLine s D)++S.R 132
      let S' : Stacks 148 A := {S with R := Function.update (Function.update S.R 110 input) 132 output}
      (∀ c, SchurDominance.Solves (realMatrix s t p u) I (R c) c) ∧
      v'.user = v.user ∧ n ≤ realInteriorResidualCost p l s t u target rhsExp a b ∧
      Exec (embTab componentReg (embTab groupReg body)) (retainedSchurResidual hR hQ) (mk v S) n (mk v' S') ∧
      (∀ i, (C i).im = 0) ∧
      (∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp)
        (8*p+1) (couplingCountExponent p u)) ∧
      (∀ i ∈ boundary, |(value q (C i)).re-SchurDominance.residual (realMatrix s t p u) I R
          (fun i => (value q (B i)).re) i| ≤
        (2*band+1)*(2/(2 : ℝ)^q)+(2*band+1)*((2 : ℝ)^stableInteriorExponent p rhsExp*(1/(2 : ℝ)^q))+
          2*(1/(2 : ℝ)^target)) ∧
      (∀ i, publishedCellRead q w (0 : ZMod s) (S'.R 110) i = (value q (C i)).re) ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l target rhsExp+1) q l s t u band 0 0 input
        (embStk componentReg S') := by
  dsimp only
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let band := PhaseCellBand.width p u
  let I := haloInterior s t band a b
  let : NeZero t := ⟨by omega⟩
  have hμ : (0 : ℝ) < 1/(8*(p : ℝ)) := by
    have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    positivity
  have hAI := SchurDominance.dominates_mono (realMatrix s t p u) Finset.univ I _ (Finset.subset_univ _)
    (matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget)
  let R := fun c : ZMod s → ℝ => Classical.choose (SchurDominance.solves_exists (realMatrix s t p u) I _ hμ hAI c)
  have hRsolve (c) : SchurDominance.Solves (realMatrix s t p u) I (R c) c := Classical.choose_spec
    (SchurDominance.solves_exists (realMatrix s t p u) I _ hμ hAI c)
  obtain ⟨v₁,n,D,hu₁,hn,he₁,hDreal,hDnorm,hDerror,hCreal,hCnorm,hCerror⟩ := realInteriorResidual_spec (body := body)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad B hB
    (R (fun i => (value q (B i)).re)) (hRsolve _) (embDn componentReg v) (embStk componentReg S) tail
    (by simpa [embStk,componentReg] using h127) (by simpa [embStk,componentReg] using h138)
    (by simpa [embStk,componentReg] using haMaster) (by simpa [embStk,componentReg] using hbMaster)
    hready (by simpa [embStk,componentReg] using h143)
  let C := couplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (B i))
  let input := cstream A w (chirpLine s C)++S.R 110
  let output := cstream A w (chirpLine s D)++S.R 132
  have he₁' : Exec (embTab groupReg body) (realInteriorResidual hR hQ)
      (mk (embDn componentReg v) (embStk componentReg S)) n
      (mk v₁ {(embStk componentReg S) with R := (Function.update
        (Function.update (embStk componentReg S).R 110 input) 132 output)}) := by
    convert he₁ using 1
    apply congrArg (mk v₁)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h110 : k = 110 <;> by_cases h132 : k = 132 <;>
      simp [h110,h132,input,output,embStk,componentReg,C,q,w,band]
  obtain ⟨v₂,hu₂,he₂⟩ := componentExec_twoPorts (body := embTab groupReg body)
    (realInteriorResidual hR hQ) v S v₁ n input output hu₁ he₁'
  refine ⟨v₂,n,D,R,hRsolve,hu₂,hn,he₂,hCreal,hCnorm,?_,?_,?_⟩
  · intro i hi
    simpa only [SchurDominance.residual,SchurDominance.couple] using hCerror i
  · intro i
    have hfits (j : ZMod s) : Fits w (C j) := fits_of_value_power
      (stableInteriorResidual_width p u l target rhsExp) (C j) (hCnorm j)
    have hread := publishedCellRead_encodedField (q := q) (w := w) (by omega : 4 ≤ A)
      (by dsimp [w,executionWidth]; omega : 0 < w) C (S.R 110) hfits i
    simpa [input,C,q,w,band] using hread
  · have hproject : embStk componentReg {S with R := Function.update (Function.update S.R 110 input) 132 output} =
        {(embStk componentReg S) with R := (Function.update (Function.update (embStk componentReg S).R 110 input) 132 output)} := by
      have hlow : embStk componentReg {S with R := Function.update S.R 110 input} =
          {(embStk componentReg S) with R := Function.update (embStk componentReg S).R 110 input} := by
        simpa [componentReg] using componentProject_updateR_inner S 110 input
      have hh := componentProject_updateR_inner {S with R := Function.update S.R 110 input} 132 output
      have hh' : embStk componentReg {S with R := Function.update (Function.update S.R 110 input) 132 output} =
          {(embStk componentReg {S with R := Function.update S.R 110 input}) with R :=
            (Function.update (embStk componentReg {S with R := Function.update S.R 110 input}).R 132 output)} := by
        simpa [componentReg] using hh
      rw [hlow] at hh'
      exact hh'
    rw [hproject]
    exact (hready.update_source input).update_output output

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
