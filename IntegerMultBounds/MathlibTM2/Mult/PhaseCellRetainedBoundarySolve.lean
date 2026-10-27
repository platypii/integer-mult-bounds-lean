module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPhysicalRetainedSchurResidual

/-! Execute retained residual production and the complete constructed boundary solve. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.BandFactor

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def retainedBoundarySolve (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 224 Q A U :=
  .seq (physicalRetainedSchurResidual hR hQ) (constructedBoundaryUnscaledSolve hR hQ)

noncomputable def retainedBoundarySolveCost (p u l s t a b target : ℕ) [NeZero s] : ℕ :=
  let bits := boundaryTableBits p target 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card
  realInteriorResidualCost p l s t u (initialSchurTarget p u bits 2) 2 a b+
    constructedBoundaryUnscaledSolveCost p u l s t a b target 2

theorem retainedBoundarySolve_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (F : ZMod s → GaussianInt) (hF : ∀ i, ‖value (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) (F i)‖ ≤ (2 : ℝ)^2)
    (v : HS 224 Q A U) (S : Stacks 224 A) (tail : List (Fin (A+4)))
    (h109 : S.R 109 = []) (h115 : S.R 115 = []) (h116 : S.R 116 = [])
    (hleft : ∀ i : Fin 224, S.L i = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u (boundaryTableBits p target 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) l s t u (PhaseCellBand.width p u) 0 0 (cstream A (executionWidth p l (initialSchurTarget p u (boundaryTableBits p target 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) (chirpLine s F)++tail) (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S)))))
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (h0 : S.R 0 = [])
    (h139 : S.R 139 = [])
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = []) (h147 : S.R 147 = []) 
    (h151 : S.R 151 = []) (h153 : S.R 153 = [])
    (h152 : S.R 152 = []) (hnew : ∀ i : Fin 224, 154 ≤ i.val → S.R i = []) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let bits := boundaryTableBits p target 2 B.card
    let band := PhaseCellBand.width p u
    let W := 12*band+1
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    ∃ v' S' n, ∃ D : ZMod s → GaussianInt, ∃ columns : List (ZMod s → GaussianInt),
    ∃ solution : List GaussianInt,
      let C := couplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (F i))
      v'.user = v.user ∧ n ≤ retainedBoundarySolveCost p u l s t a b target ∧
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
        (embTab componentReg (embTab groupReg body))))) (retainedBoundarySolve hR hQ)
        (mk v S) n (mk v' S') ∧
      columns.length = B.card ∧ solution.length = B.card ∧ (∀ z ∈ solution, Fits w z) ∧
      S'.R 217 = cstream A w solution ∧
      S'.R 110 = cstream A w (chirpLine s C)++S.R 110 ∧
      S'.R 132 = bandTableWords A w B W columns 0++cstream A w (chirpLine s D)++S.R 132 ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ i : Fin 154, i ≠ 109 → i ≠ 110 → i ≠ 115 → i ≠ 116 → i ≠ 132 →
        S'.R (boundaryFactorLegacyReg i) = S.R (boundaryFactorLegacyReg i)) ∧
      RsbReady (boundaryFactorState S') w q ∧ (S'.R 119).length = q ∧
      (∀ i : Fin 64, S'.R (boundaryFactorMulReg i) = []) ∧
      S'.R 184 = [] ∧ S'.R 223 = [] ∧ S'.R 220 = [] ∧ S'.R 221 = [] ∧
      ∀ x : ZMod s → ℝ,
      SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x (fun i => (value q (F i)).re) →
      ∀ i < B.card, ‖value q (solution.getD i 0) - (x (bFoldAt s B i) : ℂ)‖ ≤ 3/(2 : ℝ)^target ∧
        ‖value q (solution.getD i 0)‖ ≤ (2 : ℝ)^stableInteriorExponent p 2 := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let bits := boundaryTableBits p target 2 B.card
  let band := PhaseCellBand.width p u
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let W := 12*band+1
  obtain ⟨v₁,n₁,D,R,hRsolve,hu₁,hn₁,he₁,hreal,hmag,herr,hread,hready₁⟩ :=
    physicalRetainedSchurResidual_spec (body := body) (target := bits) (rhsExp := 2)
      hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad
      F hF v S tail h127 h138 h143 haMaster hbMaster hready
  let C := couplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (F i))
  let input := cstream A w (chirpLine s C)++S.R 110
  let output := cstream A w (chirpLine s D)++S.R 132
  let S₁ : Stacks 224 A := {S with R := Function.update (Function.update S.R 110 input) 132 output}
  have hframe (i : Fin 224) (hi110 : i ≠ 110) (hi132 : i ≠ 132) : S₁.R i = S.R i := by
    simp [S₁,hi110,hi132]
  have hleft₁ : ∀ i : Fin 224, S₁.L i = [] := hleft
  have hnew₁ : ∀ i : Fin 224, 154 ≤ i.val → S₁.R i = [] := by
    intro i hi
    rw [hframe i (by intro h; subst i; change 154 ≤ 110 at hi; omega)
      (by intro h; subst i; change 154 ≤ 132 at hi; omega)]
    exact hnew i hi
  have hC : ∀ i ∈ B, |gv q (C i).re| ≤ (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2)
      (8*p+1) (couplingCountExponent p u) ∧
      |gv q (C i).im| ≤ (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2)
      (8*p+1) (couplingCountExponent p u) := by
    intro i hi
    exact ⟨(Complex.abs_re_le_norm _).trans (hmag i),(Complex.abs_im_le_norm _).trans (hmag i)⟩
  obtain ⟨v₂,S₂,n₂,columns,hu₂,hn₂,he₂,hlen,hcolumns,hformat,hstorage,herror,hrank,hinp,hout,hL,hlegacy,
    hcoordinates,h115',h116',h132',hbo,hhf,hdf,hreset,hsolLen,hsolFits,hsrc,hvk,hready₂,h119,hmul,
    h184,h223,h220,h221,hacc⟩ :=
    constructedBoundaryUnscaledSolve_spec (body := body) (target := target) (rhsExp := 2)
      hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad
      v₁ S₁ input
      (by simpa [S₁] using h109) (by simpa [S₁] using h115) (by simpa [S₁] using h116)
      hleft₁ hready₁ (by simpa [S₁] using haMaster) (by simpa [S₁] using hbMaster)
      (by simpa [S₁] using h0) (by simpa [S₁] using h139) (by simpa [S₁] using h127)
      (by simpa [S₁] using h138) (by simpa [S₁] using h143) (by simpa [S₁] using h147)
      (by simpa [S₁] using h151) (by simpa [S₁] using h153) (by simpa [S₁] using h152)
      hnew₁ C (S.R 110) hC (by simp [S₁,input,w,bits,B])
  refine ⟨v₂,S₂,n₁+n₂,D,columns,_,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,
    Exec.seq he₁ he₂,hlen,hsolLen,hsolFits,hsrc,?_,?_,hinp,hout,hL,?_,
    hready₂,h119,hmul,h184,h223,h220,h221,?_⟩
  · have h := hlegacy 110 (by decide) (by decide) (by decide) (by decide)
    simpa [boundaryFactorLegacyReg,S₁,input,w,bits,B,C,q,band] using h
  · simpa [S₁,output,List.append_assoc] using h132'
  · intro i hi109 hi110 hi115 hi116 hi132
    rw [hlegacy i hi109 hi115 hi116 hi132]
    apply hframe
    · intro h
      apply hi110
      exact boundaryFactorLegacyReg_injective h
    · intro h
      apply hi132
      exact boundaryFactorLegacyReg_injective h
  · intro x hx i hi
    exact hacc R x (fun j => (value q (F j)).re) hRsolve hx
      (fun j _ => (Complex.abs_re_le_norm _).trans (hF j))
      (fun j _ => hreal j) herr i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
