module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryFactorWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryFactory
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryFactoryRelease
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryTableRouting

/-! Execute the Schur/factor supplier in the same workspace as the packed solve. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 242 Q A U}

noncomputable def routedPackedBoundaryFactoryRelease (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 242 Q A U :=
  embProg packedBoundaryTableRouting Empty.elim (packedBoundaryFactoryRelease hR hQ)

theorem routedPackedBoundaryFactoryRelease_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
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
    (h152 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 152 = []) (hnew : ∀ i : Fin 224, 154 ≤ i.val → (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R (preparedBoundaryCoreReg i) = []) (h132left : S.L 132 = []) :
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
        (2*(B.card*publicationGeometryWidth t band+publicationGeometryWidth t band+B.card)+7) ∧
      Exec body (routedPackedBoundaryFactoryRelease hR hQ) (mk v S) n (mk v' F) ∧
      F.inp = S.inp ∧ F.out = S.out ∧
      F.R 220 = bandTableWords A w B W columns 0++S.R 220 ∧
      BoundaryFactorStock (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg F)) (boundaryFactorStockBound q w band B.card) ∧
      (
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
      (∀ i : Fin 154, i ≠ 109 → i ≠ 115 → i ≠ 116 → i ≠ 132 →
        (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting F))).R (boundaryFactorLegacyReg i) =
          (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S))).R (boundaryFactorLegacyReg i)) ∧
      ∀ k : Fin 242, (∀ i, packedBoundaryFactorReg i ≠ k) →
        (embStk packedBoundaryTableRouting F).L k = (embStk packedBoundaryTableRouting S).L k ∧ (embStk packedBoundaryTableRouting F).R k = (embStk packedBoundaryTableRouting S).R k ) ∧ F.R 132 = S.R 132 ∧ F.L 132 = S.L 132 := by
  dsimp only
  obtain ⟨v₁,T₁,n,columns,hu₁,hn,he,hinputFrame,houtputFrame,hrawTable,hstock,hlen,hformat,hcolumns,hstage,hsolve,hbo,hhf,hdf,
    hvk,h224,h225,hleft',hmul,hmaster,h223,h184,h220,h221,herror,hnative,hlegacy,hframe⟩ :=
    packedBoundaryFactoryRelease_spec (body := fun p : Empty => nomatch p)
      hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad
      (embDn packedBoundaryTableRouting v) (embStk packedBoundaryTableRouting S) tail
      h109 h115 h116 hleft hready haMaster hbMaster h0 h139 h127 h138 h143 h147 h151 h153 h152 hnew
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    packedBoundaryTableRouting_injective (fun p => nomatch p) he v rfl S rfl
  let F := embOvr packedBoundaryTableRouting T₁.get S
  have hproj : embStk packedBoundaryTableRouting F = T₁ :=
    embStk_ovr packedBoundaryTableRouting_injective T₁ S
  have hoff := hframe 220 packedBoundaryFactorReg_ne_table
  have hbufferR : F.R 132 = S.R 132 := by
    have hh := (congrArg (fun B : Stacks 242 A => B.R 220) hproj).trans hoff.2
    simpa [embStk,packedBoundaryTableRouting] using hh
  have hbufferL : F.L 132 = S.L 132 := by
    have hh := (congrArg (fun B : Stacks 242 A => B.L 220) hproj).trans hoff.1
    simpa [embStk,packedBoundaryTableRouting] using hh
  have hleftReal := packedBoundaryTableRouting_left F (by rw [hproj]; exact hleft')
    (hbufferL.trans h132left)
  refine ⟨v₂,F,n,columns,hu₂.trans hu₁,hn,he₂,(by simpa [F,embOvr,embStk] using hinputFrame),
    (by simpa [F,embOvr,embStk] using houtputFrame),?_,?_,?_,hbufferR,hbufferL⟩
  · have hp := congrArg (fun G : Stacks 242 A => G.R 132) hproj
    simpa [embStk,packedBoundaryTableRouting] using hp.trans hrawTable
  · apply hstock.of_frame
    intro i hi hn
    have he206 : preparedBoundaryCoreReg i ≠ (206 : Fin 226) := by
      intro he; exact hn (Fin.ext (congrArg (fun k : Fin 226 => k.val) he))
    have hhigh := packedBoundaryFactorReg_high_range (preparedBoundaryCoreReg i) hi he206
    have hfixed := packedBoundaryTableRouting_fixed (packedBoundaryFactorReg (preparedBoundaryCoreReg i))
      (by intro he; have hh := congrArg Fin.val he; omega)
      (packedBoundaryFactorReg_ne_table _)
    have hp := congrArg (fun G : Stacks 242 A => G.R
      (packedBoundaryTableRouting (packedBoundaryFactorReg (preparedBoundaryCoreReg i)))) hproj
    simpa only [embStk,Function.comp_apply,hfixed] using hp
  rw [← packedBoundaryTableRouting_native F,← packedBoundaryTableRouting_state F,hproj]
  exact ⟨hlen,hformat,hcolumns,hstage,hsolve,hbo,hhf,hdf,hvk,h224,h225,hleftReal,hmul,
    hmaster,h223,h184,h220,h221,herror,hnative,hlegacy,hframe⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
