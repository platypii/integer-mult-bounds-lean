module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryFactoryBetween
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedFactoryInputBank

/-! Construct factor setup from ordinary headers, including full-line endpoint keys.
No separated-interval or local-solver parameter record is required. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 242 Q A U}

theorem packedFactoryInputBank_factor_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (v : HS 242 Q A U) (H : Stacks 242 A) :
    let V := publicationGeometryWidth t (PhaseCellBand.width p u)
    let entryBits := boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card
    let setupTarget := initialSchurTarget p u entryBits 2
    let S := packedFactoryInputBank H (2^15*p) (executionStagePrecision p l setupTarget 2+1)
      (executionPrecision p l setupTarget 2) l s t u (PhaseCellBand.width p u) a b V
    let band := PhaseCellBand.width p u
    let B := haloBoundary s t band a b
    let bits := boundaryTableBits p target rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let W := 12*band+1
    ∃ v' F n, ∃ columns : List (ZMod s → GaussianInt),
      v'.user = v.user ∧ n ≤ constructedBoundaryFactorCost p u l s t a b target rhsExp+
        (2*(B.card*publicationGeometryWidth t band+publicationGeometryWidth t band+B.card)+7)+
        ((s+t+band+a+b)*(4*V+10)+56*V+77) ∧
      Exec body (packedBoundaryFactoryGeometry hR hQ) (mk v S) n (mk v' F) ∧
      F.inp = S.inp ∧ F.out = S.out ∧
      F.R 110 = [] ∧ F.R 132 = S.R 132 ∧
      PreparedBoundaryColumns A p bits q w W B columns ∧
      (∀ i ∈ B, ∀ j ∈ B, |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j-
        (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
          (haloInterior s t band a b).toList).1 i j| ≤ 1/(2 : ℝ)^bits) ∧
      PackedBoundaryFactorPages
        (cstream A w ((naturalLineLc q (factorNewtonSteps p q) W B.card (factorRankIntegerMatrix B W columns)).map colC).flatten)
        (cstream A w ((naturalLineUc q (factorNewtonSteps p q) W B.card (factorRankIntegerMatrix B W columns)).map colC).flatten)
        (cstream A w ((naturalLineRcs q (factorNewtonSteps p q) W B.card (factorRankIntegerMatrix B W columns)).map fun z => (⟨z,0⟩ : GaussianInt))) F ∧
      PackedHaloBetweenInputs (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
        q l s t u band a b V w W B.card (extendStacks (by decide) F) ∧
      F.R 220 = bandTableWords A w B W columns 0++S.R 220 ∧
      BoundaryFactorStock (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg F))
        (boundaryFactorStockBound q w band B.card) := by
  dsimp only
  let V := publicationGeometryWidth t (PhaseCellBand.width p u)
  let band := PhaseCellBand.width p u
  let bits := boundaryTableBits p target rhsExp (haloBoundary s t band a b).card
  let stage := executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let S := packedFactoryInputBank H (2^15*p) stage q l s t u band a b V
  have hblank (k : Fin 242) (hk : k ∉ packedFactoryLivePorts) : S.R k = [] :=
    packedFactoryInputBank_blank_of_not_mem H (2^15*p) stage q l s t u band a b V k hk
  have hleft (k : Fin 242) : S.L k = [] :=
    packedFactoryInputBank_left H (2^15*p) stage q l s t u band a b V k
  have hnative := packedFactoryInputBank_native H (2^15*p) stage q l s t u band a b V
  have hn (i : Fin 224) (hi : ∀ j, inverseMasterCorePort j ≠ i) :
      (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg
        (embStk packedBoundaryTableRouting S))).R i = [] := by
    have hv := congrArg (fun F : Stacks 224 A => F.R i) hnative
    exact hv.trans (by
      rw [masterHeaderBank_off (masterHeaderValues (2^15*p) stage q l s t u band a b) [] i hi]
      simp)
  have hmasters (j : Fin 10) : (inverseMasterCorePort j).val < 154 := by
    fin_cases j <;> decide
  have hgeometry := packedFactoryInputBank_geometry H (2^15*p) stage q l s t u band a b V
  have ha := congrArg List.length (packedFactoryInputBank_headers H (2^15*p) stage q l s t u band a b V 8)
  have hb := congrArg List.length (packedFactoryInputBank_headers H (2^15*p) stage q l s t u band a b V 9)
  apply packedBoundaryFactoryGeometry_between_exec (body := body) hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget
    hband has hbs hpad v S []
  · exact hn 109 (by intro j; fin_cases j <;> decide)
  · exact hn 115 (by intro j; fin_cases j <;> decide)
  · exact hn 116 (by intro j; fin_cases j <;> decide)
  · exact fun i => hleft _
  · exact packedFactoryInputBank_ready H (2^15*p) stage q l s t u band a b V
  · dsimp [inverseMasterCorePort, masterHeaderValues, packedFactoryNativeReg] at ha
    simpa [S, embStk, packedBoundaryTableRouting, packedBoundaryFactorReg, preparedBoundaryCoreReg] using ha
  · dsimp [inverseMasterCorePort, masterHeaderValues, packedFactoryNativeReg] at hb
    simpa [S, embStk, packedBoundaryTableRouting, packedBoundaryFactorReg, preparedBoundaryCoreReg] using hb
  · exact hn 0 (by intro j; fin_cases j <;> decide)
  · exact hn 139 (by intro j; fin_cases j <;> decide)
  · exact hn 127 (by intro j; fin_cases j <;> decide)
  · exact hn 138 (by intro j; fin_cases j <;> decide)
  · exact hn 143 (by intro j; fin_cases j <;> decide)
  · exact hn 147 (by intro j; fin_cases j <;> decide)
  · exact hn 151 (by intro j; fin_cases j <;> decide)
  · exact hn 153 (by intro j; fin_cases j <;> decide)
  · exact hn 152 (by intro j; fin_cases j <;> decide)
  · intro i hi
    apply hn i
    intro j he
    have hv := congrArg Fin.val he
    have := hmasters j
    omega
  · exact hleft 132
  · simpa only [List.length_replicate] using congrArg List.length hgeometry.2.2
  · exact hgeometry.1
  · exact hgeometry.2.1
  · have hfit := publicationGeometryWidth_fits t band
    have hsub : b-a ≤ s := (Nat.sub_le b a).trans hbs
    have hsmall : a+((b-a)+2*band)+s ≤ 8*(t+1)^2+2*band+8 := by
      nlinarith only [has,hsub,hst]
    exact hsmall.trans_lt hfit
  · have hc : ([(145 : Fin 242),146,147,148,149,151,154,156,164]).all
        (fun k => decide (k ∉ packedFactoryLivePorts)) = true := by decide +kernel
    intro k hk
    exact hblank k (of_decide_eq_true (List.all_eq_true.mp hc k hk))
  · exact hblank 239 (by decide)
  · rw [hblank 157 (by decide)]; simp
  · have hc : ([125,127,128,129,130,131,133,134,135,136,138,139,140,143,153,158,166,167] : List (Fin 242)).all
        (fun k => decide (k ∉ packedFactoryLivePorts)) = true := by decide +kernel
    intro k hk
    exact hblank k (of_decide_eq_true (List.all_eq_true.mp hc k hk))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
