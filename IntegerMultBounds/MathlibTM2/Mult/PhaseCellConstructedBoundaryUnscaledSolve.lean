module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConstructedBoundarySolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBoundaryUnscale
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellResidualBoundaryAccuracy
public import IntegerMultBounds.NLogN.PhaseCellBoundary
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryExactBounds

/-! Construct and solve the boundary system, then undo normalization exactly on tapes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.BandFactor

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def constructedBoundaryUnscaledSolve (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 224 Q A U :=
  .seq (constructedBoundarySolve hR hQ) (generatedBoundaryUnscale hQ)

noncomputable def constructedBoundaryUnscaledSolveCost (p u l s t a b target rhsExp : ℕ) [NeZero s] : ℕ :=
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let q := executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target rhsExp B.card) 2) 2
  constructedBoundarySolveCost p u l s t a b target rhsExp+generatedBoundaryUnscaleCost q B.card

theorem constructedBoundaryUnscaledSolve_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (v : HS 224 Q A U) (S : Stacks 224 A) (tail : List (Fin (A+4)))
    (h109 : S.R 109 = []) (h115 : S.R 115 = []) (h116 : S.R 116 = [])
    (hleft : ∀ i : Fin 224, S.L i = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u (boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) l s t u (PhaseCellBand.width p u) 0 0 tail (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S)))))
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (h0 : S.R 0 = [])
    (h139 : S.R 139 = [])
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = []) (h147 : S.R 147 = []) 
    (h151 : S.R 151 = []) (h153 : S.R 153 = [])
    (h152 : S.R 152 = []) (hnew : ∀ i : Fin 224, 154 ≤ i.val → S.R i = []) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let bits := boundaryTableBits p target rhsExp B.card
    let band := PhaseCellBand.width p u
    let W := 12*band+1
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let V := publicationGeometryWidth t band
    let K := factorNewtonSteps p q
    ∀ (C : ZMod s → GaussianInt) (rhsTail : List (Fin (A+4))),
    (∀ i ∈ B, |gv q (C i).re| ≤ (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp)
      (8*p+1) (couplingCountExponent p u) ∧
      |gv q (C i).im| ≤ (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp)
      (8*p+1) (couplingCountExponent p u)) →
    S.R 110 = cstream A w (chirpLine s C)++rhsTail →
    ∃ v' S' n, ∃ columns : List (ZMod s → GaussianInt),
      let AZ := factorRankIntegerMatrix B W columns
      let xs := ((List.range B.card).map (fun j => C (bFoldAt s B j))).map (normalizeBoundaryWord q (q/2-1))
      let normalizedSolution := bandSolveVec q W (naturalLineLc q K W B.card AZ)
        (naturalLineUc q K W B.card AZ) (naturalLineRcs q K W B.card AZ) xs
      let solution := normalizedSolution.map (unscaleBoundaryWord q)
      v'.user = v.user ∧ n ≤ constructedBoundaryUnscaledSolveCost p u l s t a b target rhsExp ∧
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))))
        (constructedBoundaryUnscaledSolve hR hQ) (mk v S) n (mk v' S') ∧
      columns.length = B.card ∧
      ColumnFamilyAccurate A q w B
        (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
          (haloInterior s t band a b).toList).1 (1/(2 : ℝ)^bits) columns ∧
      ColumnFamilyFormat w columns ∧
      (bandTableWords A w B W columns 0).length ≤ B.card*(2*W+1)*w ∧
      (∀ i ∈ B, ∀ j ∈ B,
        |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j-
          (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
            (haloInterior s t band a b).toList).1 i j| ≤ 1/(2 : ℝ)^bits) ∧
      SchurDominance.StageInv (factorRankMatrix A q w B W columns) (Finset.range B.card)
        (1/(8*(p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^bits)) (2+(B.card : ℝ)*(1/(2 : ℝ)^bits)) ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ i : Fin 154, i ≠ 109 → i ≠ 115 → i ≠ 116 → i ≠ 132 →
        S'.R (boundaryFactorLegacyReg i) = S.R (boundaryFactorLegacyReg i)) ∧
      S'.R 109 = cstream A V ((bFoldOrder s B).map (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt))) ∧
      S'.R 115 = List.replicate V tick ∧ S'.R 116 = List.replicate B.card tick ∧
      S'.R 132 = bandTableWords A w B W columns 0++S.R 132 ∧
      (boundaryFactorState S') .bo = cstream A w ((naturalLineLc q K W B.card AZ).map colC).flatten ∧
      (boundaryFactorState S') .hf = cstream A w ((naturalLineUc q K W B.card AZ).map colC).flatten ∧
      (boundaryFactorState S') .df = cstream A w ((naturalLineRcs q K W B.card AZ).map fun x => (⟨x,0⟩ : GaussianInt)) ∧
      BoundarySolveReady (Function.update (boundaryFactorState S') .dout []) q w W B.card ∧
      solution.length = B.card ∧ (∀ z ∈ solution, Fits w z) ∧
      S'.R 217 = cstream A w solution ∧ S'.R 206 = [] ∧
      RsbReady (boundaryFactorState S') w q ∧ (S'.R 119).length = q ∧
      (∀ i : Fin 64, S'.R (boundaryFactorMulReg i) = []) ∧
      S'.R 184 = [] ∧ S'.R 223 = [] ∧ S'.R 220 = [] ∧ S'.R 221 = [] ∧
      boundaryUnfoldHeaderVolume (boundaryFactorState S') ≤ 12*band*w+B.card*W ∧
      BoundaryPermanentBound (boundaryFactorState S') (boundaryPermanentSizeBound q band B.card) ∧
      ∀ (R : (ZMod s → ℝ) → ZMod s → ℝ) (x b₀ : ZMod s → ℝ),
      (∀ c, SchurDominance.Solves (realMatrix s t p u) (haloInterior s t band a b) (R c) c) →
      SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x b₀ →
      (∀ j ∈ haloVertices s a b, |b₀ j| ≤ (2 : ℝ)^rhsExp) →
      (∀ j ∈ B, (C j).im = 0) →
      (∀ j ∈ B, 8*(p : ℝ)*|(value q (C j)).re -
        SchurDominance.residual (realMatrix s t p u) (haloInterior s t band a b) R b₀ j| ≤
          1/(2 : ℝ)^(recoveryTarget p bits+2)) →
      ∀ i < B.card, ‖value q (solution.getD i 0) - (x (bFoldAt s B i) : ℂ)‖ ≤
        3/(2 : ℝ)^target ∧
        ‖value q (solution.getD i 0)‖ ≤ (2 : ℝ)^stableInteriorExponent p rhsExp := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let band := PhaseCellBand.width p u
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let W := 12*band+1
  let K := factorNewtonSteps p q
  intro C rhsTail hC hRhs
  obtain ⟨v₁,S₁,n₁,columns,hu₁,hn₁,he₁,hlen,hcolumns,hformat,hstorage,herror,hrank,hinp,hout,hL,hlegacy,
    hcoordinates,h115',h116',h132',hbo,hhf,hdf,hreset,hsolLen,hsolBound,hsrc,hvk,hready',h119,hmul,h184,h223,h220,h221,hheaders,hperm⟩ :=
    constructedBoundarySolve_spec (body := body) hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad
      v S tail h109 h115 h116 hleft hready haMaster hbMaster h0 h139 h127 h138 h143 h147 h151 h153 h152 hnew C rhsTail hC hRhs
  let AZ := factorRankIntegerMatrix B W columns
  let rhs := ((List.range B.card).map (fun j => C (bFoldAt s B j))).map (normalizeBoundaryWord q (q/2-1))
  let sol := bandSolveVec q W (naturalLineLc q K W B.card AZ) (naturalLineUc q K W B.card AZ)
    (naturalLineRcs q K W B.card AZ) rhs
  have hbits : 4*p+2*Nat.size B.card+36 ≤ q := factor_execution_bits p u l target rhsExp B.card
  have hpq : p ≤ q/2 := by omega
  have hw : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  have hsource : S₁.R 217 = cstream A (2*q+8) sol := by
    change S₁.R 217 = cstream A w sol at hsrc
    rw [hw] at hsrc
    exact hsrc
  have hready'' : RsbReady (boundaryFactorState S₁) (2*q+8) q := hw ▸ hready'
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := generatedBoundaryUnscale_exec
    (body := embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))))
    hQ hA q p hpq sol hsolBound v₁ S₁ (by intro i; rw [hL]; exact hleft i) hmul hready'' h119
    h184 h220 h221 h223 (hreset.empty .ya (by simp [boundarySolveScratch]))
    (hreset.empty .ac2 (by simp [boundarySolveScratch])) hsource
  let result := sol.map (unscaleBoundaryWord q)
  let S₂ : Stacks 224 A := {S₁ with R := Function.update S₁.R 217 (cstream A w result)}
  have he₂' : Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))))
      (generatedBoundaryUnscale hQ) (mk v₁ S₁) n₂ (mk v₂ S₂) := by
    simpa only [S₂,result,hw] using he₂
  have hstate : boundaryFactorState S₂ = Function.update (boundaryFactorState S₁) .dout (cstream A w result) :=
    boundaryFactorState_update S₁ .dout _
  change sol.length = B.card at hsolLen
  rw [hsolLen] at hn₂
  have hresultFits : ∀ z ∈ result, Fits w z := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
    rw [hw]
    exact (boundary_unscale_fits q p hpq x (hsolBound x hx)).2
  have hreset' : BoundarySolveReady (Function.update (boundaryFactorState S₂) .dout []) q w W B.card := by
    rw [hstate,Function.update_idem]
    exact hreset
  have hreadyFinal : RsbReady (boundaryFactorState S₂) w q := by
    rw [hstate]
    exact hready'.update .dout (fun _ => by simp) _
  have hmulFinal (i : Fin 64) : S₂.R (boundaryFactorMulReg i) = [] := by
    have hi217 : boundaryFactorMulReg i ≠ 217 := by
      intro hi
      have hv := congrArg (fun k : Fin 224 => k.val) hi
      have hi' := i.isLt
      change i.val = 217 at hv
      omega
    simpa only [S₂,Function.update_of_ne hi217] using hmul i
  have hheadersFinal : boundaryUnfoldHeaderVolume (boundaryFactorState S₂) ≤ 12*band*w+B.card*W := by
    rw [hstate]
    simpa only [boundaryUnfoldHeaderVolume_update_dout] using hheaders
  have hpermFinal : BoundaryPermanentBound (boundaryFactorState S₂) (boundaryPermanentSizeBound q band B.card) := by
    rw [hstate]
    exact hperm.update .dout (by simp [boundaryTransientRoles]) _
  refine ⟨v₂,S₂,n₁+n₂,columns,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂',hlen,hcolumns,hformat,
    hstorage,herror,hrank,hinp,hout,hL,?_,?_,?_,?_,?_,?_,?_,?_,hreset',?_,hresultFits,?_,?_,hreadyFinal,?_,hmulFinal,?_,?_,?_,?_,hheadersFinal,hpermFinal,?_⟩
  · intro i hi109 hi115 hi116 hi132
    have hi217 : boundaryFactorLegacyReg i ≠ 217 := by
      intro hi
      have hv := congrArg (fun k : Fin 224 => k.val) hi
      have hi' := i.isLt
      change i.val = 217 at hv
      omega
    exact (Function.update_of_ne hi217 _ _).trans (hlegacy i hi109 hi115 hi116 hi132)
  · simpa [S₂] using hcoordinates
  · simpa [S₂] using h115'
  · simpa [S₂] using h116'
  · simpa [S₂] using h132'
  · rw [hstate]; exact hbo
  · rw [hstate]; exact hhf
  · rw [hstate]; exact hdf
  · simpa only [List.length_map] using hsolLen
  · rfl
  · simpa [S₂] using hvk
  · simpa [S₂] using h119
  · simpa [S₂] using h184
  · simpa [S₂] using h223
  · simpa [S₂] using h220
  · simpa [S₂] using h221
  · intro R x b₀ hRsolve hx hb₀ hreal herr i hi
    let I := haloInterior s t band a b
    have hU : I ∪ B = haloVertices s a b := haloInterior_union_boundary s t band a b
    let M := realMatrix s t p u
    let : NeZero t := ⟨by omega⟩
    have hM : SchurDominance.DominatesOn M (I ∪ B) (1/(8*(p : ℝ))) := by
      rw [hU]
      exact SchurDominance.dominates_mono M Finset.univ (haloVertices s a b) _
        (Finset.subset_univ _) (matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget)
    have hx' : SchurDominance.Solves M (I ∪ B) x b₀ := by rw [hU]; exact hx
    have hb' : ∀ j ∈ I ∪ B, |b₀ j| ≤ (2 : ℝ)^rhsExp := by rw [hU]; exact hb₀
    have he' : ∀ i ∈ B, ∀ j ∈ B,
        |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j -
          (SchurDominance.run M (I ∪ B) I.toList).1 i j| ≤ 1/(2 : ℝ)^bits := by
      rw [hU]
      exact herror
    exact (boundary_residual_solution_accuracy A p u l target rhsExp B W columns hp (by omega) hlen
      C hformat hrank M I (haloInterior_disjoint_boundary s t band a b) hM R hRsolve
      x b₀ hx' hb' he' hC hreal herr).2 i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
