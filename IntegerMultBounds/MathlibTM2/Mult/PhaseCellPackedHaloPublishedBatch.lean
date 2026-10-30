module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloPublishExec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCoreArchiveFromDimensions

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {Q A : ℕ} {P U : Type}

variable {body : P → Pr P 242 Q A U} {body' : P → Pr P 248 Q A U}
  {body'' : P → Pr P 249 Q A U} {bodyLarge : P → Pr P 263 Q A U}

theorem packedHaloPublishedBatch_exec
    (hbody : ∀ f, body' f = embProg packedBoundaryRecoveryBase id (body f))
    (hbody' : ∀ f, body'' f = embProg packedHaloBatchReg id (body' f))
    (hbody'' : ∀ f, bodyLarge f = embProg packedHaloPublishedReg id (body'' f))
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u boundaryTarget target finalTarget rhsExp a b V : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (inputs : List ((ZMod s → GaussianInt) × (ZMod s → ℝ)))
    (tail : List (Fin (A+4))) (v : HS 263 Q A U) (Sbig : Stacks 263 A) (S₀ : Stacks 249 A) (S : Stacks 242 A)
    (hview : embStk packedHaloBatchReg S₀ = extendStacks (by decide) S)
    (hcount : (S₀.R 248).length = inputs.length)
    (h109 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 109 = []) (h115 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 115 = []) (h116 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 116 = [])
    (hfactoryLeft : ∀ i : Fin 224, (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).L (preparedBoundaryCoreReg i) = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u
      (boundaryTableBits p boundaryTarget rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u
        (boundaryTableBits p boundaryTarget rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)
      l s t u (PhaseCellBand.width p u) 0 0 ((inputs.map (fun x => cstream A (executionWidth p l target rhsExp)
        (packedInterval a (b-a) x.1))).flatten++tail)
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S))))))))
    (haMaster : ((embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 141).length = a) (hbMaster : ((embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 142).length = b)
    (h0 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 0 = []) (h139 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 139 = []) (h127 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 127 = []) (h138 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 138 = [])
    (h143 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 143 = []) (h147 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 147 = []) (h151 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 151 = []) (h153 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 153 = [])
    (h152 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 152 = []) (hnew : ∀ i : Fin 224, 154 ≤ i.val → (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R (preparedBoundaryCoreReg i) = []) (h132left : S.L 132 = [])
    (hV : (S.R 163).length = V)
    (h155 : S.R 155 = binSyms V a) (h165 : S.R 165 = binSyms V (b-a))
    (hfitV : a+((b-a)+2*PhaseCellBand.width p u)+s < 2^V)
    (hgeometryBlank : ∀ k ∈ [(145 : Fin 242),146,147,148,149,151,154,156,164], S.R k = [])
    (h239 : S.R 239 = []) (h157 : (S.R 157).length ≤ V)
    (hscratch : ∀ k ∈ ([125,127,128,129,130,131,133,134,135,136,138,139,140,143,153,158,166,167] : List (Fin 242)), S.R k = [])
    (hab : a ≤ b) (haLt : a < s) (hsep : b-a+PhaseCellBand.width p u ≤ s)
    (hwide : 8*(t+1)^2+4*PhaseCellBand.width p u+8 < 2^V)
    (hVeq : V = weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (2*executionPrecision p l target rhsExp+8) t u)
    (hwV : executionWidth p l target rhsExp < 2^V)
    (hcoords : b < 2^V) (hunits : b*executionWidth p l target rhsExp < 2^V)
    (hC : ∀ x ∈ inputs, ∀ k, ‖value (executionPrecision p l target rhsExp) (x.1 k)‖ ≤ (2 : ℝ)^rhsExp)
    (hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))))
    (hcell : target = boundaryHaloTarget p u boundaryTarget rhsExp
      (haloBoundary s t (PhaseCellBand.width p u) a b).card)
    (hboundary : boundaryTarget = boundaryRecoveryTarget p finalTarget)
    (hbigview : embStk packedHaloPublishedReg Sbig = S₀)
    (coreWidth k radius : ℕ) (haEq : a = coreStart coreWidth k-radius)
    (hbEq : b = coreStart coreWidth k+coreLength s coreWidth k+radius)
    (hleft : radius ≤ coreStart coreWidth k)
    (hright : coreStart coreWidth k+coreLength s coreWidth k+radius ≤ s)
    (hRdim : (Sbig.R 249).length = radius)
    (hLdim : (Sbig.R 250).length = coreLength s coreWidth k)
    (hNdim : (Sbig.R 251).length = inputs.length)
    (hpublicationClean : ∀ i ∈ ([254,255,256,257,258,259,260,261,262] : List (Fin 263)), Sbig.R i = []) :
    let band := PhaseCellBand.width p u
    let B := haloBoundary s t band a b
    let bits := boundaryTableBits p boundaryTarget rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let W := 12*band+1
    (Sbig.R 252).length = w →
    (∀ x ∈ inputs, SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x.2
      (fun k => (value q (x.1 k)).re)) →
    (∀ j < b-a, ∀ z ∈ couplingCoefficientWords (2^15*p) q s t u band (a+j), Fits w z ∧ z.im = 0) →
    ∃ v' F n, v'.user = v.user ∧
      n ≤ constructedBoundaryFactorCost p u l s t a b boundaryTarget rhsExp+
        (2*(B.card*publicationGeometryWidth t band+publicationGeometryWidth t band+B.card)+7)+
        ((s+t+band+a+b)*(4*V+10)+56*V+77)+
        packedHaloBatchCost inputs.length
          (packedFreshOutputCost V (b-a) w+packedHaloPreparedInputCost p u l finalTarget rhsExp s t a b V)+
        (retirePackedBandTableCost B.card W w+packedFactorReleaseCost (boundaryFactorStockBound q w band B.card))+packedCoreBatchPublicationCost inputs.length radius (coreLength s coreWidth k) w ∧
      Exec bodyLarge (packedHaloPublishedBatch hR hQ) (mk v Sbig) n (mk v' F) ∧
      F.R 132 = S.R 132 ∧ F.R 110 = tail ∧ F.R 220 = S.R 220 ∧ F.R 248 = [] ∧
      (∀ i ∈ packedFactorOwnedRegs, F.R (Fin.castLE (by decide) i) = []) ∧
      (∀ i : Fin 263, 249 ≤ i.val → i ≠ 253 → F.R i = Sbig.R i) ∧
      ∃ Ds : List (ZMod s → GaussianInt),
        F.R 253 = (Ds.map (fun D => cstream A w (ownedCoreWords coreWidth k D))).flatten++Sbig.R 253 ∧
        List.Forall₂ (fun x D => PhaseCellInterface.ErrorOn (ownedCore s coreWidth k)
          (fun i => (packedIntervalRead q w (coreStart coreWidth k)
            (cstream A w (ownedCoreWords coreWidth k D)++Sbig.R 253) i).re)
          x.2 (1/(2 : ℝ)^finalTarget)) inputs Ds := by
  dsimp only
  intro hwdim hy hcoeff
  let band := PhaseCellBand.width p u
  let B := haloBoundary s t band a b
  let bits := boundaryTableBits p boundaryTarget rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  obtain ⟨v₁,H,n₁,hu₁,hn₁,he₁,hcounter,hlength,hsrc,htable,hfactors,Ds,houtputs,hgood,hclosedStock⟩ :=
    packedHaloClosedBatch_exec hbody hbody' hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget
      hband has hbs hpad inputs tail (embDn packedHaloPublishedReg v) S₀ S hview hcount h109 h115 h116 hfactoryLeft hready
      haMaster hbMaster h0 h139 h127 h138 h143 h147 h151 h153 h152 hnew h132left hV h155 h165 hfitV hgeometryBlank
      h239 h157 hscratch hab haLt hsep hwide hVeq hwV hcoords hunits hC hdom hcell hboundary hy hcoeff
  obtain ⟨v₂,F,n,hu₂,hn,he,harchive,hdst,hcoreGood,hkeep,hexternal,hpublicationStock⟩ :=
    packedHaloClosedBatch_publish_exec hbody'' hR hQ q w a b coreWidth k radius haEq hbEq hleft hright
      inputs Ds (1/(2 : ℝ)^finalTarget) (S.R 132) he₁ hcounter houtputs hgood v Sbig rfl hbigview
      hRdim hLdim hNdim hwdim hpublicationClean
  refine ⟨v₂,F,n,hu₂.trans hu₁,hn.trans (Nat.add_le_add_right hn₁ _),he,harchive,?_,?_,?_,?_,hexternal,Ds,hdst,hcoreGood⟩
  · exact (hkeep 110 (by decide)).trans hsrc
  · exact (hkeep 220 (by decide)).trans htable
  · exact (hkeep 248 (by decide)).trans hcounter
  · intro i hi
    have hb := packedFactorOwnedRegs_bounds i hi
    have h132 : (Fin.castLE (by decide : 248 ≤ 249) i) ≠ 132 := by
      intro he; have hh := congrArg Fin.val he; change i.val = 132 at hh; omega
    exact (hkeep (Fin.castLE (by decide) i) h132).trans (hfactors i hi)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
