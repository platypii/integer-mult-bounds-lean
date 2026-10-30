module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloGeneratedPublishedBatch
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

noncomputable def packedHaloGeometryPublishedBatch (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 263 Q A U :=
  .seq (.seq (.seq (prepareCoreDimensions 252 165 249 250 254 255 259) (uclear 252))
    (packedHaloGeneratedPublishedBatch hR hQ)) (clearWords [249,250])

/-- Shared workspace for one geometry-prepared batch. Numerical scratch is
paid once; retained archives are charged separately. -/
noncomputable def packedHaloGeometryWorkspace
    (p u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius count : ℕ) [NeZero s] : ℕ :=
  let band := PhaseCellBand.width p u
  let B := haloBoundary s t band a b
  let bits := boundaryTableBits p boundaryTarget rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let W := 12*band+1
  ((prepareCoreDimensionsCost V (coreLength s coreWidth k+2*radius) radius+(2*V+2))+((8*q+9)+((4*count+4)+(constructedBoundaryFactorCost p u l s t a b boundaryTarget rhsExp+
                (2*(B.card*publicationGeometryWidth t band+publicationGeometryWidth t band+B.card)+7)+
                ((s+t+band+a+b)*(4*V+10)+56*V+77)+
                (packedFreshOutputCost V (b-a) w+packedHaloPreparedInputCost p u l finalTarget rhsExp s t a b V)+
                (retirePackedBandTableCost B.card W w+packedFactorReleaseCost (boundaryFactorStockBound q w band B.card))+
                100*(count+1)*((coreLength s coreWidth k+2*radius)*w+1)))+(2*w+2))+(2*(radius+coreLength s coreWidth k)+5))

variable {body : P → Pr P 242 Q A U} {body' : P → Pr P 248 Q A U}
  {body'' : P → Pr P 249 Q A U} {bodyLarge : P → Pr P 263 Q A U}

theorem packedHaloGeometryPublishedBatch_exec
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
    (hcounterBlank : S₀.R 248 = [])
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
    ∃ v' F n, v'.user = v.user ∧
      n ≤ (prepareCoreDimensionsCost V (coreLength s coreWidth k+2*radius) radius+(2*V+2))+((8*q+9)+((4*inputs.length+4)+(constructedBoundaryFactorCost p u l s t a b boundaryTarget rhsExp+
        (2*(B.card*publicationGeometryWidth t band+publicationGeometryWidth t band+B.card)+7)+
        ((s+t+band+a+b)*(4*V+10)+56*V+77)+
        packedHaloBatchCost inputs.length
          (packedFreshOutputCost V (b-a) w+packedHaloPreparedInputCost p u l finalTarget rhsExp s t a b V)+
        (retirePackedBandTableCost B.card W w+packedFactorReleaseCost (boundaryFactorStockBound q w band B.card))+packedCoreBatchPublicationCost inputs.length radius (coreLength s coreWidth k) w))+(2*w+2))+(2*(radius+coreLength s coreWidth k)+5) ∧
      Exec bodyLarge (packedHaloGeometryPublishedBatch hR hQ) (mk v Sbig) n (mk v' F) ∧
      F.inp = Sbig.inp ∧ F.out = Sbig.out ∧
      F.R 132 = S.R 132 ∧ F.R 110 = tail ∧ F.R 220 = S.R 220 ∧ F.R 248 = [] ∧ F.R 252 = [] ∧
      (∀ i ∈ packedFactorOwnedRegs, F.R (Fin.castLE (by decide) i) = []) ∧
      (∀ i : Fin 263, 249 ≤ i.val → i ≠ 252 → i ≠ 253 → F.R i = Sbig.R i) ∧
      ∃ Ds : List (ZMod s → GaussianInt),
        F.R 253 = (Ds.map (fun D => cstream A w (ownedCoreWords coreWidth k D))).flatten++Sbig.R 253 ∧
        List.Forall₂ (fun x D => PhaseCellInterface.ErrorOn (ownedCore s coreWidth k)
          (fun i => (packedIntervalRead q w (coreStart coreWidth k)
            (cstream A w (ownedCoreWords coreWidth k D)++Sbig.R 253) i).re)
          x.2 (1/(2 : ℝ)^finalTarget)) inputs Ds ∧
        ∀ c, mnProgPush (packedHaloGeometryPublishedBatch (P := P) (U := U) (A := A) hR hQ) ≤ c →
          (∀ f, mnProgPush (bodyLarge f) ≤ c) → ∀ depth,
          ExecWithin bodyLarge (fun d z => mnSize z+d ≤ mnSize (mk v Sbig)+
            (inputs.length*((b-a)*w)+V)+depth+(c+1)*
              packedHaloGeometryWorkspace p u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius inputs.length)
            depth (packedHaloGeometryPublishedBatch hR hQ) (mk v Sbig) n (mk v' F) := by
  dsimp only
  intro hradiusWord hy hcoeff
  have hlen : b-a = coreLength s coreWidth k+2*radius := by omega
  have h165big : Sbig.R 165 = binSyms V (coreLength s coreWidth k+2*radius) := by
    have h₁ := congrArg (fun T : Stacks 249 A => T.R 165) hbigview
    have h₂ := congrArg (fun T : Stacks 248 A => T.R 165) hview
    change Sbig.R 165 = S₀.R 165 at h₁
    change S₀.R 165 = (extendStacks (by decide : 242 ≤ 248) S).R 165 at h₂
    rw [h₁,h₂]
    change S.R 165 = _
    exact h165.trans (congrArg (fun n => binSyms V n) hlen)
  have hhalo : coreLength s coreWidth k+2*radius < 2^V := by omega
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := prepareCoreDimensions_exec (body := bodyLarge)
    (radiusWord := 252) (lengthWord := 165) (radius := 249) (rows := 250)
    (work := 254) (saved := 255) (tmp := 259) (by decide) V (coreLength s coreWidth k) radius
    (by omega) hhalo v Sbig hradiusWord h165big (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl
      · exact h249
      · exact h250
      · exact hpublicationClean 254 (by decide)
      · exact hpublicationClean 255 (by decide)
      · exact hpublicationClean 259 (by decide))
  let M : Stacks 263 A := {Sbig with R := (Function.update (Function.update Sbig.R 249
    (List.replicate radius tick)) 250 (List.replicate (coreLength s coreWidth k) tick))}
  obtain ⟨v₂,hu₂,he₂⟩ := uclear_exec bodyLarge 252 v₁ M
  have hwordLen : (M.R 252).length = V := by simp [M,hradiusWord,length_binSyms]
  rw [hwordLen] at he₂
  let Tbig : Stacks 263 A := {M with R := Function.update M.R 252 []}
  have hbigview₁ : embStk packedHaloPublishedReg Tbig = S₀ := by
    have hoff (x : Fin 263) (hx : 249 ≤ x.val) : ∀ i, packedHaloPublishedReg i ≠ x := by
      intro i he
      have hh := congrArg (fun i : Fin 263 => i.val) he
      have hi := i.isLt
      change i.val = x.val at hh
      omega
    let S₁ : Stacks 263 A := {Sbig with R := Function.update Sbig.R 249 (List.replicate radius tick)}
    have hT : embStk packedHaloPublishedReg Tbig = embStk packedHaloPublishedReg M :=
      embStk_updateR_off M 252 [] (hoff 252 (by decide))
    have hM : embStk packedHaloPublishedReg M = embStk packedHaloPublishedReg S₁ :=
      embStk_updateR_off S₁ 250 (List.replicate (coreLength s coreWidth k) tick) (hoff 250 (by decide))
    have hS₁ : embStk packedHaloPublishedReg S₁ = embStk packedHaloPublishedReg Sbig :=
      embStk_updateR_off Sbig 249 (List.replicate radius tick) (hoff 249 (by decide))
    exact hT.trans (hM.trans (hS₁.trans hbigview))
  obtain ⟨v₃,F,n₃,hu₃,hn₃,he₃,hinput,houtput,harchive,hsrc,htable,hcounter,hfactors,hexternal,Ds,hdst,hgood,hgeneratedStock⟩ :=
    packedHaloGeneratedPublishedBatch_exec hbody hbody' hbody'' hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget
      hband has hbs hpad inputs tail v₂ Tbig S₀ S hview hcounterBlank h109 h115 h116 hfactoryLeft hready
      haMaster hbMaster h0 h139 h127 h138 h143 h147 h151 h153 h152 hnew h132left hV h155 h165 hfitV hgeometryBlank
      h239 h157 hscratch hab haLt hsep hwide hVeq hwV hcoords hunits hC hdom hcell hboundary
      hbigview₁ coreWidth k radius haEq hbEq hleft hright
      (by simp [Tbig,M]) (by simp [Tbig,M]) (by simpa [Tbig,M] using hNdim)
      (by
        intro i hi
        have h249' : i ≠ 249 ∧ i ≠ 250 ∧ i ≠ 252 := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        simpa only [Tbig,M,Function.update_of_ne h249'.1,Function.update_of_ne h249'.2.1,
          Function.update_of_ne h249'.2.2] using hpublicationClean i hi)
      (by simp [Tbig]) hy hcoeff
  have h249F : (F.R 249).length = radius := by
    rw [hexternal 249 (by decide) (by decide)]
    simp [Tbig,M]
  have h250F : (F.R 250).length = coreLength s coreWidth k := by
    rw [hexternal 250 (by decide) (by decide)]
    simp [Tbig,M]
  obtain ⟨v₄,hu₄,he₄⟩ := clearWords_exec (body := bodyLarge) [249,250] (by decide) v₃ F
  have hcleanTime : 2*([(249 : Fin 263),250].map (fun i => (F.R i).length)).sum+2*([(249 : Fin 263),250]).length+1 =
      2*(radius+coreLength s coreWidth k)+5 := by simp [h249F,h250F]
  rw [hcleanTime] at he₄
  let G : Stacks 263 A := {F with R := fun i => if i ∈ [(249 : Fin 263),250] then [] else F.R i}
  refine ⟨v₄,G,((n₁+(2*V+2))+n₃)+(2*(radius+coreLength s coreWidth k)+5),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)),
    Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_right hn₁ _) hn₃) _,
    Exec.seq (Exec.seq (Exec.seq he₁ he₂) he₃) he₄,hinput,houtput,?_,?_,?_,?_,?_,?_,?_,Ds,?_,?_,?_⟩
  · exact harchive
  · exact hsrc
  · exact htable
  · exact hcounter
  · change F.R 252 = []
    exact hexternal 252 (by decide) (by decide)
  · intro i hi
    have hb := packedFactorOwnedRegs_bounds i hi
    have hnot : (Fin.castLE (by decide : 248 ≤ 263) i) ∉ [(249 : Fin 263),250] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff,Fin.val_castLE]
      omega
    simpa only [G,ite_eq_right hnot] using hfactors i hi
  · intro i hi h252 h253
    by_cases h249' : i = 249
    · subst i; exact h249.symm
    by_cases h250' : i = 250
    · subst i; exact h250.symm
    have hn : i ∉ [(249 : Fin 263),250] := by simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]; exact ⟨h249',h250'⟩
    simpa only [G,ite_eq_right hn,Tbig,M,Function.update_of_ne h252,Function.update_of_ne h250',
      Function.update_of_ne h249'] using hexternal i hi h253
  · simpa [G,Tbig,M] using hdst
  · simpa [Tbig,M] using hgood
  · intro c hpLarge hbLarge depth
    have hpParts := hpLarge
    simp only [packedHaloGeometryPublishedBatch,mnProgPush] at hpParts
    have hpSetup := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_left _ _) hpParts)
    have hpGenerated := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_left _ _) hpParts)
    have hpRelease := Nat.le_trans (Nat.le_max_right _ _) hpParts
    have ht := hgeneratedStock c hpGenerated hbLarge depth
    have htSetup := mn_setup_exec_within_stock (Exec.seq he₁ he₂)
      (Nat.add_le_add_right hn₁ _) hpSetup hbLarge ht
    simpa only [packedHaloGeometryPublishedBatch,packedHaloGeometryWorkspace] using
      (mn_release_exec_within_stock htSetup he₄ (Nat.le_refl _) hpRelease hbLarge)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
