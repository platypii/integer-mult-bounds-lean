module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProtectedPackedHaloBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedKeyInputViews
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedKeyPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCoreDimensions
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateWordWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCoreArchiveFromDimensions

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {Q A : ℕ} {P U : Type}

variable {body : P → Pr P 242 Q A U} {body' : P → Pr P 248 Q A U}
  {body'' : P → Pr P 249 Q A U} {bodyLarge : P → Pr P 263 Q A U}

noncomputable def packedHaloBatchCostFromSetup
    (p u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius count : ℕ) [NeZero s] : ℕ :=
  let band := PhaseCellBand.width p u
  let B := haloBoundary s t band a b
  let bits := boundaryTableBits p boundaryTarget rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let W := 12*band+1
  (prepareCoreDimensionsCost V (coreLength s coreWidth k+2*radius) radius+(2*V+2))+((8*q+9)+((4*count+4)+(constructedBoundaryFactorCost p u l s t a b boundaryTarget rhsExp+
        (2*(B.card*publicationGeometryWidth t band+publicationGeometryWidth t band+B.card)+7)+
        ((s+t+band+a+b)*(4*V+10)+56*V+77)+
        packedHaloBatchCost count
          (packedFreshOutputCost V (b-a) w+packedHaloPreparedInputCost p u l finalTarget rhsExp s t a b V)+
        (retirePackedBandTableCost B.card W w+packedFactorReleaseCost (boundaryFactorStockBound q w band B.card))+packedCoreBatchPublicationCost count radius (coreLength s coreWidth k) w))+(2*w+2))+(2*(radius+coreLength s coreWidth k)+5)

theorem packedHaloBatch_from_setup_exec
    (hbody : ∀ f, body' f = embProg packedBoundaryRecoveryBase id (body f))
    (hbody' : ∀ f, body'' f = embProg packedHaloBatchReg id (body' f))
    (hbody'' : ∀ f, bodyLarge f = embProg packedHaloPublishedReg id (body'' f))
    (bodyProtected : P → Pr P 276 Q A U)
    (hbodyProtected : ∀ f, bodyProtected f = embProg packedKeySolverReg id (bodyLarge f))
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u boundaryTarget target finalTarget rhsExp a b V : ℕ} [NeZero s] {α d : ℝ}
    (inputs : List ((ZMod s → GaussianInt) × (ZMod s → ℝ)))
    (C : ZMod s → GaussianInt)
    (tail : List (Fin (A+4))) (v : HS 276 Q A U) (Sprotected : Stacks 276 A) (Sbig : Stacks 263 A) (S₀ : Stacks 249 A) (S : Stacks 242 A)
    (hviews : PackedKeyBankViews Sprotected Sbig S₀ S)
    (hcounterBlank : S₀.R 248 = [])
    (hsetup : PackedHaloSetup (p := p) (l := l) (t := t) (u := u) (target := finalTarget)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α d C S)
    (hsource : S.R 110 = (inputs.map (fun x => cstream A (executionWidth p l target rhsExp)
      (packedInterval a (b-a) x.1))).flatten++tail)
    (hscratch : ∀ k ∈ ([125,127,128,129,130,131,133,134,135,136,138,139,140,143,153,158,166,167] : List (Fin 242)), S.R k = [])
    (hC : ∀ x ∈ inputs, ∀ k, ‖value (executionPrecision p l target rhsExp) (x.1 k)‖ ≤ (2 : ℝ)^rhsExp)
    (hcell : target = boundaryHaloTarget p u boundaryTarget rhsExp
      (haloBoundary s t (PhaseCellBand.width p u) a b).card)
    (hboundary : boundaryTarget = boundaryRecoveryTarget p finalTarget)
    (coreWidth k radius : ℕ) (haEq : a = coreStart coreWidth k-radius)
    (hbEq : b = coreStart coreWidth k+coreLength s coreWidth k+radius)
    (hleft : radius ≤ coreStart coreWidth k)
    (hright : coreStart coreWidth k+coreLength s coreWidth k+radius ≤ s)
    (h249 : Sbig.R 249 = []) (h250 : Sbig.R 250 = [])
    (hNdim : (Sbig.R 251).length = inputs.length)
    (hpublicationClean : ∀ i ∈ ([254,255,256,257,258,259,260,261,262] : List (Fin 263)), Sbig.R i = []) :
    let band := PhaseCellBand.width p u
    let B := haloBoundary s t band a b
    let bits := boundaryTableBits p boundaryTarget rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let W := 12*band+1
    Sbig.R 252 = binSyms V radius →
    (∀ x ∈ inputs, SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x.2
      (fun k => (value q (x.1 k)).re)) →
    (∀ j < b-a, ∀ z ∈ couplingCoefficientWords (2^15*p) q s t u band (a+j), Fits w z ∧ z.im = 0) →
    ∃ v' F G n, v'.user = v.user ∧
      n ≤ packedHaloBatchCostFromSetup p u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius inputs.length ∧
      Exec bodyProtected (embProg packedKeySolverReg id (packedHaloGeometryPublishedBatch hR hQ))
        (mk v Sprotected) n (mk v' G) ∧
      G.inp = Sprotected.inp ∧ G.out = Sprotected.out ∧
      embStk packedKeySolverReg G = F ∧
      (∀ j : Fin 276, 263 ≤ j.val → G.L j = Sprotected.L j ∧ G.R j = Sprotected.R j) ∧
      F.R 132 = S.R 132 ∧ F.R 110 = tail ∧ F.R 220 = S.R 220 ∧ F.R 248 = [] ∧ F.R 252 = [] ∧
      (∀ i ∈ packedFactorOwnedRegs, F.R (Fin.castLE (by decide) i) = []) ∧
      (∀ i : Fin 263, 249 ≤ i.val → i ≠ 252 → i ≠ 253 → F.R i = Sbig.R i) ∧
      ∃ Ds : List (ZMod s → GaussianInt),
        G.R 253 = (Ds.map (fun D => cstream A w (ownedCoreWords coreWidth k D))).flatten++Sprotected.R 253 ∧
        Ds.length = inputs.length ∧
        List.Forall₂ (fun x D => PhaseCellInterface.ErrorOn (ownedCore s coreWidth k)
          (fun i => (packedIntervalRead q w (coreStart coreWidth k)
            (cstream A w (ownedCoreWords coreWidth k D)++Sprotected.R 253) i).re)
          x.2 (1/(2 : ℝ)^finalTarget)) inputs Ds ∧
        ∀ c, mnProgPush (embProg packedKeySolverReg id (packedHaloGeometryPublishedBatch (P := P) (U := U) (A := A) hR hQ)) ≤ c →
          (∀ f, mnProgPush (bodyProtected f) ≤ c) → ∀ depth,
          ExecWithin bodyProtected (fun d z => mnSize z+d ≤ mnSize (mk v Sprotected)+
            (inputs.length*((b-a)*w)+V)+depth+(c+1)*
              packedHaloGeometryWorkspace p u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius inputs.length)
            depth (embProg packedKeySolverReg id (packedHaloGeometryPublishedBatch hR hQ)) (mk v Sprotected) n (mk v' G) := by
  dsimp only
  intro hradiusWord hy hcoeff
  exact protectedPackedHaloGeometryPublishedBatch_exec hbody hbody' hbody'' bodyProtected hbodyProtected
    hR hQ hA hsetup.hp hsetup.hwidth hsetup.hα hsetup.hst hsetup.hu hsetup.hαu hsetup.hθ hsetup.hgap hsetup.hbudget
    hsetup.hband hsetup.has hsetup.hbs hsetup.hpad inputs tail v Sprotected Sbig S₀ S hviews.protectedView hviews.batchView hcounterBlank
    hsetup.h109 hsetup.h115 hsetup.h116 hsetup.hleft
    (by simpa only [hsource,hboundary] using hsetup.hreadyBase)
    hsetup.haMaster hsetup.hbMaster hsetup.h0 hsetup.h139 hsetup.h127 hsetup.h138 hsetup.h143
    hsetup.h147 hsetup.h151 hsetup.h153 hsetup.h152 hsetup.hnew hsetup.h132left
    hsetup.hV hsetup.h155 hsetup.h165 hsetup.hfitV hsetup.hgeometryBlank hsetup.h239 hsetup.h157 hscratch
    hsetup.hab hsetup.haLt hsetup.hsep hsetup.hwide
    (by simpa only [hcell,hboundary] using hsetup.hVeq)
    (by simpa only [hcell,hboundary] using hsetup.hwV)
    hsetup.hcoords (by simpa only [hcell,hboundary] using hsetup.hunits)
    hC hsetup.hdom hcell hboundary hviews.publicationView coreWidth k radius haEq hbEq hleft hright
    h249 h250 hNdim hpublicationClean hradiusWord hy hcoeff

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
