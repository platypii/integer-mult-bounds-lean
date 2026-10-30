module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedFactoryGeometry
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryFactoryGeometry
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedRetainedCouplingIntervalMetadata

/-! Execute the factor supplier, native cleanup and canonical geometry setup in
one machine. The caller's packed publication buffer is retained throughout. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 242 Q A U}

noncomputable def packedBoundaryFactoryGeometryUsing (freshGeometry : Bool)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 242 Q A U :=
  if freshGeometry then packedBoundaryFactoryGeometry hR hQ else routedPackedBoundaryFactoryRelease hR hQ

theorem packedBoundaryFactoryGeometryUsing_spec (freshGeometry : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp a b V : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (v : HS 242 Q A U) (S : Stacks 242 A) (tail : List (Fin (A+4)))
    (h109 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 109 = []) (h115 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 115 = []) (h116 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 116 = [])
    (hleft : ∀ i : Fin 224, (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).L (preparedBoundaryCoreReg i) = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u
      (boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u
        (boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)
      l s t u (PhaseCellBand.width p u) 0 0 tail
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S))))))))
    (haMaster : ((embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 141).length = a) (hbMaster : ((embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 142).length = b)
    (h0 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 0 = []) (h139 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 139 = []) (h127 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 127 = []) (h138 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 138 = [])
    (h143 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 143 = []) (h147 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 147 = []) (h151 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 151 = []) (h153 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 153 = [])
    (h152 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 152 = []) (hnew : ∀ i : Fin 224, 154 ≤ i.val → (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R (preparedBoundaryCoreReg i) = []) (h132left : S.L 132 = [])
    (hV : (S.R 163).length = V)
    (h155 : S.R 155 = binSyms V a) (h165 : S.R 165 = binSyms V (b-a))
    (hfitV : a+((b-a)+2*PhaseCellBand.width p u)+s < 2^V)
    (hgeometry : if freshGeometry then
      (∀ k ∈ [(145 : Fin 242),146,147,148,149,151,154,156,164], S.R k = [])
      else CouplingIntervalMetadata V s t (PhaseCellBand.width p u) a b a (b-a)
        (embStk packedHaloRuntimeReg S)) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let bits := boundaryTableBits p target rhsExp B.card
    let band := PhaseCellBand.width p u
    let W := 12*band+1
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    ∃ v' F n, ∃ columns : List (ZMod s → GaussianInt),
      let σ := boundaryFactorState (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg F))
      let AZ := factorRankIntegerMatrix B W columns
      v'.user = v.user ∧ n ≤ constructedBoundaryFactorCost p u l s t a b target rhsExp+
        (2*(B.card*publicationGeometryWidth t band+publicationGeometryWidth t band+B.card)+7)+
        (if freshGeometry then (s+t+band+a+b)*(4*V+10)+56*V+77 else 0) ∧
      Exec body (packedBoundaryFactoryGeometryUsing freshGeometry hR hQ) (mk v S) n (mk v' F) ∧
      F.inp = S.inp ∧ F.out = S.out ∧
      F.R 220 = bandTableWords A w B W columns 0++S.R 220 ∧
      BoundaryFactorStock (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg F)) (boundaryFactorStockBound q w band B.card) ∧
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
      (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting F)).R 206 = [] ∧ (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting F)).R 224 = (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 224 ∧ (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting F)).R 225 = (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 225 ∧
      (∀ i : Fin 224, (embStk packedBoundaryFactorReg F).L (preparedBoundaryCoreReg i) = []) ∧
      (∀ i : Fin 64, (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting F)).R (preparedBoundaryCoreReg (boundaryFactorMulReg i)) = []) ∧
      ((embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting F)).R 119).length = q ∧ (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting F)).R 223 = [] ∧ (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting F)).R 184 = [] ∧ (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting F)).R 220 = [] ∧ (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting F)).R 221 = [] ∧
      (∀ i ∈ B, ∀ j ∈ B,
        |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j-
          (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
            (haloInterior s t band a b).toList).1 i j| ≤ 1/(2 : ℝ)^bits) ∧
      embStk packedCellCoreReg (embStk packedHaloRuntimeReg F) =
        releasedCellBank [] tail ((embStk packedBoundaryTableRouting F).R 93) (embStk packedBoundaryTableRouting F).inp (embStk packedBoundaryTableRouting F).out ∧
      CouplingIntervalMetadata V s t band a b a (b-a) (embStk packedHaloRuntimeReg F) ∧
      F.R 132 = S.R 132 ∧ F.R 93 = S.R 93 ∧
      ∀ k : Fin 242, 117 ≤ k.val → k.val < 168 → k ≠ 143 →
        k ∉ packedBoundaryGeometryPorts → F.R k = S.R k := by
  cases freshGeometry with
  | true =>
    exact packedBoundaryFactoryGeometry_spec hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad
      v S tail h109 h115 h116 hleft hready haMaster hbMaster h0 h139 h127 h138 h143 h147 h151 h153 h152 hnew h132left hV h155 h165 hfitV hgeometry
  | false =>
    obtain ⟨v',F,n,columns,hu',hn,he,hin,hout,hraw,hstock,hlen,hformat,hcolumns,hstage,
      hsolve,hbo,hhf,hdf,h206,h224,h225,hleft',hmul,hmaster,h223,h184,h220,h221,herror,
      hnative,hmeta,hbuffer,h93,hframe⟩ :=
      routedPackedBoundaryFactoryRetainedGeometry_spec hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad
      v S tail h109 h115 h116 hleft hready haMaster hbMaster h0 h139 h127 h138 h143 h147 h151 h153 h152 hnew h132left hgeometry
    refine ⟨v',F,n,columns,hu',?_,he,hin,hout,hraw,hstock,hlen,hformat,hcolumns,hstage,
      hsolve,hbo,hhf,hdf,h206,h224,h225,hleft',hmul,hmaster,h223,h184,h220,h221,herror,
      hnative,hmeta,hbuffer,h93,?_⟩
    · simpa only [Bool.false_eq_true,ite_false,Nat.add_zero] using hn
    · intro k hk hk' h143 _
      exact hframe k hk hk' h143

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
