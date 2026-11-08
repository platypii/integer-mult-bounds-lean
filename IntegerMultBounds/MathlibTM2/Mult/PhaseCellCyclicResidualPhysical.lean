module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicResidualPasses
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellEmbeddedOutput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorInput
public import IntegerMultBounds.NLogN.PhaseCellCyclicResidualPieces

/-! Execute both guarded interior residuals against the same retained RHS. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def cyclicResidualPhysical (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 224 Q A U :=
  embProg boundaryFactorLegacyReg id (embProg tableReg id (embProg boundaryArithmeticReg id
    (cyclicResidualPasses hR hQ)))

theorem cyclicResidualPhysical_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp a n : ℕ} [NeZero s] {alpha d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (halpha : 0 < alpha) (hst : s < t) (hu : 1 ≤ u)
    (hsquare : alpha^2 = (u : ℝ)) (htheta : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : alpha^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (ha : a < s) (hn : n ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (B : ZMod s → GaussianInt)
    (hB : ∀ i, ‖value (executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp) (B i)‖ ≤ (2 : ℝ)^rhsExp)
    (v : HS 224 Q A U) (S : Stacks 224 A) (tail : List (Fin (A+4)))
    (haSrc : (S.R 144).length = a) (hleftEnd : (S.R 145).length = a+min n (s-a))
    (hrightEnd : (S.R 146).length = n-min n (s-a))
    (hfresh : ∀ k ∈ [(127 : Fin 224),138,141,142,143,147], S.R k = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1)
      (executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp) (chirpLine s B)++tail) (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S))))) :
    let q := executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp
    let w := executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp
    let band := PhaseCellBand.width p u
    ∃ v' m, ∃ C D : ZMod s → GaussianInt, ∃ R T : (ZMod s → ℝ) → ZMod s → ℝ,
      let output := cstream A w (chirpLine s D)++(cstream A w (chirpLine s C)++S.R 132)
      let S' : Stacks 224 A := {S with R := Function.update S.R 132 output}
      (∀ rhs, SchurDominance.Solves (realMatrix s t p u)
        (cyclicPrincipalInterior s t band a n)
        (fun k => if k ∈ haloInterior s t band a (a+min n (s-a)) then R rhs k else T rhs k) rhs) ∧
      v'.user = v.user ∧ m ≤ windowedSchurResidualCost p l s t u target rhsExp a (a+min n (s-a))+
        windowedSchurResidualCost p l s t u target rhsExp 0 (n-min n (s-a)) ∧
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
        (embTab componentReg (embTab groupReg body))))) (cyclicResidualPhysical hR hQ) (mk v S) m (mk v' S') ∧
      (∀ i, (C i).im = 0 ∧ (D i).im = 0) ∧
      (∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u) ∧
        ‖value q (D i)‖ ≤ (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u)) ∧
      (∀ i ∈ cyclicPrincipalBoundary s t band a n,
        |(if i ∈ haloVertices s a (a+min n (s-a)) then (value q (C i)).re else (value q (D i)).re)-
          SchurDominance.residual (realMatrix s t p u) (cyclicPrincipalInterior s t band a n)
            (fun rhs k => if k ∈ haloInterior s t band a (a+min n (s-a)) then R rhs k else T rhs k)
            (fun k => (value q (B k)).re) i| ≤ (1/(2 : ℝ)^(recoveryTarget p target+2))/(8*(p : ℝ))) ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1)
        q l s t u band 0 0 (S.R 110) (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S')))) := by
  dsimp only
  let E := embStk boundaryFactorLegacyReg S
  let F := embStk tableReg E
  let G := embStk boundaryArithmeticReg F
  obtain ⟨vi,m,C,D,R,T,hsolve,huser,hm,he,hreal,hnorm,herror,hready'⟩ :=
    cyclicResidualPasses_spec (body := body) hR hQ hA hp hwidth halpha hst hu hsquare htheta hgap hbudget hband ha hn hpad B hB
      (embDn boundaryArithmeticReg (embDn tableReg (embDn boundaryFactorLegacyReg v))) G tail
      (by simpa [G,F,E,embStk,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using haSrc)
      (by simpa [G,F,E,embStk,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using hleftEnd)
      (by simpa [G,F,E,embStk,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using hrightEnd)
      (by intro k hk
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
            simpa [G,F,E,embStk,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using hfresh _ (by simp)) hready
  let q := executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp
  let w := executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp
  let output := cstream A w (chirpLine s D)++(cstream A w (chirpLine s C)++S.R 132)
  have he' : Exec (embTab componentReg (embTab groupReg body)) (cyclicResidualPasses hR hQ)
      (mk (embDn boundaryArithmeticReg (embDn tableReg (embDn boundaryFactorLegacyReg v))) G) m
      (mk vi {G with R := Function.update G.R 132 output}) := by
    simpa [G,F,E,embStk,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,output,w] using he
  obtain ⟨v₁,hv₁,he₁⟩ := embeddedOutput_exec boundaryArithmeticReg boundaryArithmeticReg_injective
    (cyclicResidualPasses hR hQ) (embDn tableReg (embDn boundaryFactorLegacyReg v)) F vi m 132 output he'
  obtain ⟨v₂,hv₂,he₂⟩ := embeddedOutput_exec tableReg tableReg_injective
    (embProg boundaryArithmeticReg id (cyclicResidualPasses hR hQ)) (embDn boundaryFactorLegacyReg v) E v₁ m 132 output he₁
  obtain ⟨v₃,hv₃,he₃⟩ := embeddedOutput_exec boundaryFactorLegacyReg boundaryFactorLegacyReg_injective
    (embProg tableReg id (embProg boundaryArithmeticReg id (cyclicResidualPasses hR hQ))) v S v₂ m 132 output he₂
  refine ⟨v₃,m,C,D,R,T,hsolve,hv₃.trans (hv₂.trans (hv₁.trans huser)),hm,he₃,hreal,hnorm,herror,?_⟩
  have p₁ := embeddedOutput_project boundaryFactorLegacyReg boundaryFactorLegacyReg_injective S 132 output
  have p₂ := embeddedOutput_project tableReg tableReg_injective E 132 output
  have p₃ := embeddedOutput_project boundaryArithmeticReg boundaryArithmeticReg_injective F 132 output
  change embStk boundaryFactorLegacyReg {S with R := Function.update S.R 132 output} = _ at p₁
  change embStk tableReg {E with R := Function.update E.R 132 output} = _ at p₂
  change embStk boundaryArithmeticReg {F with R := Function.update F.R 132 output} = _ at p₃
  change LengthKeyReady _ _ _ _ _ _ _ _ _ _ (S.R 110)
    (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
      (embStk boundaryFactorLegacyReg {S with R := Function.update S.R 132 output}))))
  rw [p₁,p₂,p₃]
  exact hready'

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
