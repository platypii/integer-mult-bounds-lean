module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryFactorWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryFactory
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleasePackedBoundaryRuntime

/-! Execute the Schur/factor supplier in the same workspace as the packed solve. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 242 Q A U}

noncomputable def packedBoundaryFactoryRelease (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 242 Q A U :=
  .seq (packedBoundaryFactory hR hQ) releasePackedBoundaryRuntime

theorem packedBoundaryFactoryRelease_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (v : HS 242 Q A U) (S : Stacks 242 A) (tail : List (Fin (A+4)))
    (h109 : (embStk packedBoundaryFactorReg S).R 109 = []) (h115 : (embStk packedBoundaryFactorReg S).R 115 = []) (h116 : (embStk packedBoundaryFactorReg S).R 116 = [])
    (hleft : ∀ i : Fin 224, (embStk packedBoundaryFactorReg S).L (preparedBoundaryCoreReg i) = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u
      (boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u
        (boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)
      l s t u (PhaseCellBand.width p u) 0 0 tail
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg S)))))))
    (haMaster : ((embStk packedBoundaryFactorReg S).R 141).length = a) (hbMaster : ((embStk packedBoundaryFactorReg S).R 142).length = b)
    (h0 : (embStk packedBoundaryFactorReg S).R 0 = []) (h139 : (embStk packedBoundaryFactorReg S).R 139 = []) (h127 : (embStk packedBoundaryFactorReg S).R 127 = []) (h138 : (embStk packedBoundaryFactorReg S).R 138 = [])
    (h143 : (embStk packedBoundaryFactorReg S).R 143 = []) (h147 : (embStk packedBoundaryFactorReg S).R 147 = []) (h151 : (embStk packedBoundaryFactorReg S).R 151 = []) (h153 : (embStk packedBoundaryFactorReg S).R 153 = [])
    (h152 : (embStk packedBoundaryFactorReg S).R 152 = []) (hnew : ∀ i : Fin 224, 154 ≤ i.val → (embStk packedBoundaryFactorReg S).R (preparedBoundaryCoreReg i) = []) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let bits := boundaryTableBits p target rhsExp B.card
    let band := PhaseCellBand.width p u
    let W := 12*band+1
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    ∃ v' S' n, ∃ columns : List (ZMod s → GaussianInt),
      let σ := boundaryFactorState (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg S'))
      let AZ := factorRankIntegerMatrix B W columns
      v'.user = v.user ∧ n ≤ constructedBoundaryFactorCost p u l s t a b target rhsExp+
        (2*(B.card*publicationGeometryWidth t band+publicationGeometryWidth t band+B.card)+7) ∧
      Exec body (packedBoundaryFactoryRelease hR hQ) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧
      S'.R 132 = bandTableWords A w B W columns 0++S.R 132 ∧
      BoundaryFactorStock (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg S')) (boundaryFactorStockBound q w band B.card) ∧
      columns.length = B.card ∧ ColumnFamilyFormat w columns ∧
      ColumnFamilyAccurate A q w B
        (SchurDominance.run (realMatrix s t p u) (haloVertices s a b) (haloInterior s t band a b).toList).1
        (1/(2 : ℝ)^bits) columns ∧
      SchurDominance.StageInv (factorRankMatrix A q w B W columns) (Finset.range B.card)
        (1/(8*(p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^bits)) (2+(B.card : ℝ)*(1/(2 : ℝ)^bits)) ∧
      BoundarySolveReady σ q w W B.card ∧
      σ .bo = cstream A w ((naturalLineLc q K W B.card AZ).map colC).flatten ∧
      σ .hf = cstream A w ((naturalLineUc q K W B.card AZ).map colC).flatten ∧
      σ .df = cstream A w ((naturalLineRcs q K W B.card AZ).map fun x => (⟨x,0⟩ : GaussianInt)) ∧
      (embStk packedBoundaryFactorReg S').R 206 = [] ∧ (embStk packedBoundaryFactorReg S').R 224 = (embStk packedBoundaryFactorReg S).R 224 ∧ (embStk packedBoundaryFactorReg S').R 225 = (embStk packedBoundaryFactorReg S).R 225 ∧
      (∀ i : Fin 224, (embStk packedBoundaryFactorReg S').L (preparedBoundaryCoreReg i) = []) ∧
      (∀ i : Fin 64, (embStk packedBoundaryFactorReg S').R (preparedBoundaryCoreReg (boundaryFactorMulReg i)) = []) ∧
      ((embStk packedBoundaryFactorReg S').R 119).length = q ∧ (embStk packedBoundaryFactorReg S').R 223 = [] ∧ (embStk packedBoundaryFactorReg S').R 184 = [] ∧ (embStk packedBoundaryFactorReg S').R 220 = [] ∧ (embStk packedBoundaryFactorReg S').R 221 = [] ∧
      (∀ i ∈ B, ∀ j ∈ B,
        |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j-
          (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
            (haloInterior s t band a b).toList).1 i j| ≤ 1/(2 : ℝ)^bits) ∧
      embStk packedCellCoreReg (embStk packedHaloRuntimeReg S') =
        releasedCellBank [] tail (S'.R 93) S'.inp S'.out ∧
      (∀ i : Fin 154, i ≠ 109 → i ≠ 115 → i ≠ 116 → i ≠ 132 →
        (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg S')).R (boundaryFactorLegacyReg i) =
          (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg S)).R (boundaryFactorLegacyReg i)) ∧
      ∀ k : Fin 242, (∀ i, packedBoundaryFactorReg i ≠ k) →
        S'.L k = S.L k ∧ S'.R k = S.R k := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let band := PhaseCellBand.width p u
  let V := publicationGeometryWidth t band
  obtain ⟨v₁,S₁,n₁,columns,hu₁,hn₁,he₁,hinputFrame,houtputFrame,hrawTable,hstock,hlen,hformat,hcolumns,hstage,hsolve,hbo,hhf,hdf,
    hvk,h224,h225,hleft',hmul,hmaster,h223,h184,h220,h221,herror,
    ⟨hruntime,h109len,h115len,h116len,hlegacy⟩,hframe⟩ := packedBoundaryFactory_spec
      (body := body) hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad
      v S tail h109 h115 h116 hleft hready haMaster hbMaster h0 h139 h127 h138 h143 h147 h151 h153 h152 hnew
  obtain ⟨v₂,hu₂,he₂⟩ := releasePackedBoundaryRuntime_exec (body := body) B.card V v₁ S₁
    h109len h115len h116len
  let F := releasedPackedBoundaryRuntime S₁
  have hstate := releasedPackedBoundaryRuntime_factorState S₁
  have hnative := releasedPackedBoundaryRuntime_native S₁ tail (fun i => by
    have hh := hleft' ⟨i.val,by have hi := i.isLt; omega⟩
    have hi := i.isLt
    simpa [embStk,preparedBoundaryCoreReg,packedBoundaryFactorReg,Fin.ext_iff,
      show i.val ≠ 140 by omega,show i.val ≠ 143 by omega,show i.val ≠ 206 by omega,
      show i.val < 154 by omega] using hh) hruntime
  refine ⟨v₂,F,n₁+(2*(B.card*V+V+B.card)+7),columns,hu₂.trans hu₁,
    Nat.add_le_add_right hn₁ _,Exec.seq he₁ he₂,
    (by simpa [F,releasedPackedBoundaryRuntime] using hinputFrame),
    (by simpa [F,releasedPackedBoundaryRuntime] using houtputFrame),
    (by simpa [F,releasedPackedBoundaryRuntime] using hrawTable),
    packedBoundaryFactorStock_of_high_frame S₁ F
      (releasedPackedBoundaryRuntime_high S₁) hstock,hlen,hformat,hcolumns,hstage,?_,?_,?_,?_,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,herror,?_,?_,?_⟩
  · rw [hstate]; exact hsolve
  · rw [hstate]; exact hbo
  · rw [hstate]; exact hhf
  · rw [hstate]; exact hdf
  · simpa [F,embStk,packedBoundaryFactorReg,releasedPackedBoundaryRuntime] using hvk
  · simpa [F,embStk,packedBoundaryFactorReg,releasedPackedBoundaryRuntime] using h224
  · simpa [F,embStk,packedBoundaryFactorReg,releasedPackedBoundaryRuntime] using h225
  · exact hleft'
  · intro i
    have hi := i.isLt
    have hh := hmul i
    simpa [F,embStk,preparedBoundaryCoreReg,boundaryFactorMulReg,packedBoundaryFactorReg,
      releasedPackedBoundaryRuntime,Fin.ext_iff,
      show i.val ≠ 109 by omega,show i.val ≠ 115 by omega,show i.val ≠ 116 by omega,
      show i.val ≠ 140 by omega,show i.val ≠ 143 by omega,show i.val ≠ 206 by omega,
      show i.val < 154 by omega] using hh
  · simpa [F,embStk,packedBoundaryFactorReg,releasedPackedBoundaryRuntime] using hmaster
  · simpa [F,embStk,packedBoundaryFactorReg,releasedPackedBoundaryRuntime] using h223
  · simpa [F,embStk,packedBoundaryFactorReg,releasedPackedBoundaryRuntime] using h184
  · simpa [F,embStk,packedBoundaryFactorReg,releasedPackedBoundaryRuntime] using h220
  · simpa [F,embStk,packedBoundaryFactorReg,releasedPackedBoundaryRuntime] using h221
  · exact hnative
  · intro i hi109 hi115 hi116 hi132
    have h109' : preparedBoundaryCoreReg (boundaryFactorLegacyReg i) ≠ 109 := by
      intro he; exact hi109 (Fin.ext (congrArg (fun j : Fin 226 => j.val) he))
    have h115' : preparedBoundaryCoreReg (boundaryFactorLegacyReg i) ≠ 115 := by
      intro he; exact hi115 (Fin.ext (congrArg (fun j : Fin 226 => j.val) he))
    have h116' : preparedBoundaryCoreReg (boundaryFactorLegacyReg i) ≠ 116 := by
      intro he; exact hi116 (Fin.ext (congrArg (fun j : Fin 226 => j.val) he))
    exact (releasedPackedBoundaryRuntime_reg S₁ _ h109' h115' h116').trans
      (hlegacy i hi109 hi115 hi116 hi132)
  · intro k hk
    have hk109 : k ≠ 109 := by intro he; subst k; exact hk 109 rfl
    have hk115 : k ≠ 115 := by intro he; subst k; exact hk 115 rfl
    have hk116 : k ≠ 116 := by intro he; subst k; exact hk 116 rfl
    simpa [F,releasedPackedBoundaryRuntime,hk109,hk115,hk116] using hframe k hk

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
