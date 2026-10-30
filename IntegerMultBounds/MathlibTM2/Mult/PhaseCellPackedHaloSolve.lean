module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloBoundarySolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryRelease
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedTableRelease
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedFactorRelease
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedPreparedInputRelease

/-! The local nonseam halo solver: original input, boundary solve, recovery and owned-page release. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 242 Q A U} {body' : P → Pr P 248 Q A U}

/-- One packed input with an already constructed factor bank and retained
geometry. The caller owns initialization, publication and final page release. -/
noncomputable def packedHaloPreparedInput (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 248 Q A U :=
  .seq (embProg packedBoundaryRecoveryBase id
    (.seq (placedPackedHaloRealBoundaryData hR hQ) (packedPreparedResidualSolve hQ)))
    (.seq (packedBoundaryRecovery hR hQ) packedPreparedInputRelease)

/-- Retained tables and factors are released once, after the input batch. -/
noncomputable def packedHaloFinalRelease : Pr P 248 Q A U :=
  .seq packedTableRelease packedFactorRelease

noncomputable def packedHaloSolveUsing (freshGeometry : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 248 Q A U :=
  .seq (embProg packedBoundaryRecoveryBase id (packedHaloBoundarySolveUsing freshGeometry hR hQ))
    (.seq (packedBoundaryRecovery hR hQ) (.seq packedRecoveryRelease packedHaloFinalRelease))

noncomputable def packedHaloSolveUsingCost (freshGeometry : Bool) (p u l target rhsExp s t a b V : ℕ) [NeZero s] : ℕ :=
  let band := PhaseCellBand.width p u
  let B := haloBoundary s t band a b
  let targetB := boundaryRecoveryTarget p target
  let j := boundaryHaloTarget p u targetB rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u
    (boundaryTableBits p targetB rhsExp B.card) 2) 2
  let w := executionWidth p l (initialSchurTarget p u
    (boundaryTableBits p targetB rhsExp B.card) 2) 2
  (constructedBoundaryFactorCost p u l s t a b targetB rhsExp+
    (2*(B.card*publicationGeometryWidth t band+publicationGeometryWidth t band+B.card)+7)+
    (if freshGeometry then (s+t+band+a+b)*(4*V+10)+56*V+77 else 0)+
    packedHaloRealBoundaryDataCost p l s t u j rhsExp a b V+
    preparedResidualSolveCost q w B.card (12*band+1))+
    packedBoundaryRecoveryCost p u l target rhsExp s t a b V q w+
    packedRecoveryReleaseCost
      (couplingCoefficientPageInterval (2^15*p) q s t u band a b a (b-a)).length (2*band+1) w+retirePackedBandTableCost B.card (12*band+1) w+
    packedFactorReleaseCost (boundaryFactorStockBound q w band B.card)

/-- The original first-entry program initializes geometry. -/
noncomputable def packedHaloSolve (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 248 Q A U :=
  packedHaloSolveUsing true hR hQ

noncomputable def packedHaloSolveCost (p u l target rhsExp s t a b V : ℕ) [NeZero s] : ℕ :=
  packedHaloSolveUsingCost true p u l target rhsExp s t a b V

theorem packedHaloSolveUsing_spec (freshGeometry : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hbody : ∀ f, body' f = embProg packedBoundaryRecoveryBase id (body f))
    {p l s t u target rhsExp a b V : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (C : ZMod s → GaussianInt) (tail E outputTail : List (Fin (A+4)))
    (v : HS 248 Q A U) (S : Stacks 242 A)
    (h109 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 109 = []) (h115 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 115 = []) (h116 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 116 = [])
    (hleft : ∀ i : Fin 224, (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).L (preparedBoundaryCoreReg i) = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u
      (boundaryTableBits p (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u
        (boundaryTableBits p (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)
      l s t u (PhaseCellBand.width p u) 0 0 (cstream A (executionWidth p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) (packedInterval a (b-a) C)++tail)
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
        (embStk packedHaloRuntimeReg S))
    (h239 : S.R 239 = [])
    (hab : a ≤ b) (haLt : a < s) (hsep : b-a+PhaseCellBand.width p u ≤ s)
    (hwide : 8*(t+1)^2+4*PhaseCellBand.width p u+8 < 2^V)
    (hVeq : V = weightWorkspaceWidth (2^15*p) (executionPrecision p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) (2*(executionPrecision p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp)+8) t u)
    (hwV : (executionWidth p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) < 2^V) (hcoords : b < 2^V) (hunits : b*(executionWidth p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) < 2^V)
    (hC : ∀ k, ‖value (executionPrecision p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (h157 : (S.R 157).length ≤ V) (h158 : S.R 158 = []) (h167 : S.R 167 = [])
    (houtput : S.R 132 = E++outputTail) (hE : E.length = (b-a)*(executionWidth p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp))
    (hfresh : ∀ k ∈ [(125 : Fin 168),127,130,133,138,129,131,134,135,136,140,153,166],
      (embStk packedHaloRuntimeReg S).R k = [])
    (hrange : EncodedRange A (executionWidth p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) (executionPrecision p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp)
      (interiorOutputExponent p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) E)
    (hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))))
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x
      (fun k => (value (executionPrecision p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) (C k)).re)) :
    let band := PhaseCellBand.width p u
    let B := haloBoundary s t band a b
    let bits := boundaryTableBits p (boundaryRecoveryTarget p target) rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    ∃ v' F n, ∃ D : ZMod s → GaussianInt,
      v'.user = v.user ∧
      n ≤ packedHaloSolveUsingCost freshGeometry p u l target rhsExp s t a b V ∧
      Exec body' (packedHaloSolveUsing freshGeometry hR hQ) (mk v (extendStacks (by decide) S)) n (mk v' F) ∧
      F.inp = S.inp ∧ F.out = S.out ∧
      F.R 93 = S.R 93 ∧ F.R 238 = S.R 238 ∧
      F.R 138 = [] ∧ F.R 139 = [] ∧ F.R 140 = [] ∧ F.R 220 = S.R 220 ∧
      (∀ i ∈ packedFactorOwnedRegs, F.R i = []) ∧
      (F.R 130).length = w ∧ F.R 104 = [] ∧ F.R 105 = [] ∧ F.R 109 = [] ∧
      F.R 132 = cstream A w (packedInterval a (b-a) D)++outputTail ∧
      (∀ i, Fits w (D i)) ∧
      PhaseCellInterface.ErrorOn (haloVertices s a b)
        (fun i => (packedIntervalRead q w a (F.R 132) i).re) x (1/(2 : ℝ)^target) ∧
      PackedHaloNativeClean (embStk packedRecoveryRuntimeReg F) ∧
      PackedHaloRetainedHeaders (2^15*p)
        (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
        q l s t u band a b V w (embStk packedRecoveryRuntimeReg F) ∧
      ∃ residual : List (Fin (A+4)), residual.length = (b-a)*w ∧
        F.R 110 = residual++(cstream A w (packedInterval a (b-a) C)++tail) := by
  dsimp only
  let band := PhaseCellBand.width p u
  let B := haloBoundary s t band a b
  let targetB := boundaryRecoveryTarget p target
  let bits := boundaryTableBits p targetB rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  obtain ⟨xI,hxI⟩ := SchurDominance.solves_exists (realMatrix s t p u)
    (haloInterior s t band a b) (1/(8*(p : ℝ))) (by positivity)
    (SchurDominance.dominates_mono _ Finset.univ _ _ (Finset.subset_univ _) hdom)
    (fun i => (value (executionPrecision p l (boundaryHaloTarget p u targetB rhsExp B.card) rhsExp) (C i)).re)
  obtain ⟨v₁,F₁,n₁,columns,D₁,hu₁,hn₁,he₁,hinputFrame,houtputFrame,hrawTable,hstock,hlen,hformat,hcolumns,hstage,hsolve,h143,hsolution,h93,
    houtput₁,hsource,hpage,hcount,hrows,hmeta,hwork,hboundaryCount,hmask,hnative,hheaders,
    hstageMaster,hlevel,hclean,hDnorm,hDfits,herror,hylen,hyfits,hsemantic⟩ :=
    packedHaloBoundarySolveUsing_exec (body := body) freshGeometry hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget
      hband has hbs hpad C tail E outputTail (embDn packedBoundaryRecoveryBase v) S
      h109 h115 h116 hleft hready haMaster hbMaster h0 h139 h127 h138 h143 h147 h151 h153 h152 hnew
      h132left hV h155 h165 hfitV hgeometry h239 hab haLt hsep hwide hVeq hwV hcoords hunits
      hC h157 h158 h167 houtput hE hfresh hrange hdom xI hxI
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_extendStacks (by decide : 242 ≤ 248) hbody he₁ v rfl
  let G := extendStacks (by decide : 242 ≤ 248) F₁
  have hq : executionPrecision p l (boundaryHaloTarget p u targetB rhsExp B.card) rhsExp = q :=
    (boundaryHaloTarget_sizing p u l targetB rhsExp B.card).1
  have hw : executionWidth p l (boundaryHaloTarget p u targetB rhsExp B.card) rhsExp = w :=
    (boundaryHaloTarget_sizing p u l targetB rhsExp B.card).2.2
  dsimp only [targetB,B,band] at hq hw
  have hC' : ∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^rhsExp := by simpa only [hq] using hC
  have hx' : SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x
      (fun i => (value q (C i)).re) := by simpa only [hq] using hx
  have hruntime : embStk packedRecoveryRuntimeReg G = embStk packedHaloRuntimeReg F₁ := by
    refine Stacks.ext rfl rfl ?_ ?_
    · funext i
      simp [G,embStk,extendStacks,packedRecoveryRuntimeReg,packedHaloRuntimeReg,
        show i.val < 242 by have hi := i.isLt; omega]
    · funext i
      simp [G,embStk,extendStacks,packedRecoveryRuntimeReg,packedHaloRuntimeReg,
        show i.val < 242 by have hi := i.isLt; omega]
  have hlocal : a+(b-a) ≤ s := by omega
  have hwcoef : q+(8*p+1)+2 ≤ w := by
    dsimp [q,w,bits,B,band,targetB,executionPrecision,executionWidth,executionExponent,inputExponent,sourceExponent]
    omega
  have hcoeff : ∀ j < b-a, ∀ z ∈ couplingCoefficientWords (2^15*p) q s t u band (a+j),
      Fits w z ∧ z.im = 0 := by
    intro j _ z hz
    have hh := couplingCoefficientWords_bounds (by omega : 0 < p) (NeZero.pos s) hst hαu
      (lt_of_lt_of_le (by positivity : 0 < 1/(4*(p : ℝ))) hθ) hgap hbudget z hz
    exact ⟨fits_of_value_power hwcoef z hh.1,hh.2⟩
  have hs := hsemantic x hx'
  obtain ⟨v₃,F,n₂,D,hu₃,hn₂,he₃,h93',h139',h238,hin,hout,houtput',hfits,haccuracy,hbuffers,hnativeRecovery,hleft',hretained,hworkRecovery,hreadyRecovery,hprivateHeaders,hfactors⟩ :=
    packedBoundaryRecovery_spec (body := body') hR hQ hA hp hu hwidth hα hst hαu hθ hgap hbudget hdom
      hab hbs hband hsep hpad rfl rfl C _ x hC' hylen hyfits hs.1 hx' (S.R 238)
      (cstream A w (packedInterval a (b-a) D₁)) outputTail
      (cstream A w (packedInterval a (b-a)
        (guardedCouplingRowField (2^15*p) q t u band a b false D₁ C))) tail
      (by simp only [length_cstream,packedInterval_length _ hlocal]; rfl) (by simp only [length_cstream,packedInterval_length _ hlocal]; rfl)
      v₂ G (by simpa [G,packedBoundaryRecoveryBase] using hwork)
      (by simpa [G,packedBoundaryRecoveryBase] using hsolve)
      (by simpa [G,extendStacks] using h143)
      (by simpa [G,extendStacks] using hboundaryCount)
      (by simpa [G,extendStacks] using hsolution)
      (by change (embStk packedRecoveryRuntimeReg G).R 165 = _; rw [hruntime]; exact hmeta.count)
      (by simpa [G,extendStacks] using hmask)
      (by simpa [G,extendStacks] using houtput₁)
      (by simpa [G,extendStacks] using hsource)
      (fun i hi => (extendStacks_fresh (by decide) F₁ i hi).1)
      (fun i hi => (extendStacks_fresh (by decide) F₁ i hi).2)
      (by rw [hruntime]; exact hheaders)
      (by simpa [G,extendStacks] using hstageMaster)
      (by simpa [G,extendStacks] using hlevel)
      (by
        intro i hi93 hi110 hi116
        have hi : i.val < 242 := by have hh := i.isLt; omega
        simpa only [G,extendStacks,dite_eq_left hi] using hnative i hi93 hi110 hi116)
      (by
        intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simpa [G,extendStacks] using hclean _ (by decide))
      (by simpa [G,extendStacks] using congrArg List.length hrows)
      (by simpa [G,extendStacks] using hpage)
      (by simpa [G,extendStacks] using congrArg List.length hcount)
      hcoeff hwide hfitV (by simpa only [hq] using hVeq)
      (by simpa only [hw] using hwV) hcoords (by simpa only [hw] using hunits)
      (by rw [hruntime]; exact hmeta)
  let page := couplingCoefficientPageInterval (2^15*p) q s t u band a b a (b-a)
  have hreleaseScratch : ∀ i ∈ ([104,105,106,107,108,109,111,112] : List (Fin 248)),
      F.R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hnativeRecovery 104 (by decide) (by decide)
    · exact hnativeRecovery 105 (by decide) (by decide)
    · exact hnativeRecovery 106 (by decide) (by decide)
    · exact hnativeRecovery 107 (by decide) (by decide)
    · exact hnativeRecovery 108 (by decide) (by decide)
    · exact hnativeRecovery 109 (by decide) (by decide)
    · exact hnativeRecovery 111 (by decide) (by decide)
    · exact hnativeRecovery 112 (by decide) (by decide)
  have hcount' : (F.R 139).length = page.length := by
    rw [h139']
    simpa [G,extendStacks,page,q,bits,B,band,targetB] using congrArg List.length hcount
  have hrows' : (F.R 140).length = 2*band+1 := by
    rw [hretained 140 (by decide)]
    simpa [G,extendStacks] using congrArg List.length hrows
  have hwidth' : (F.R 130).length = w := by
    rw [hretained 130 (by decide)]
    simpa [G,extendStacks,embStk,packedHaloRuntimeReg] using hheaders.width
  have hpage' : F.R 138 = cstream A w page++[] := by
    rw [hretained 138 (by decide)]
    simpa [G,extendStacks,page] using hpage
  obtain ⟨v₄,n₃,hu₄,hn₃,he₄⟩ := packedRecoveryRelease_exec (body := body') w (2*band+1) page [] v₃ F
    hcount' hrows' hwidth' hpage' (hreleaseScratch 109 (by decide))
    (hreleaseScratch 104 (by decide)) (hreleaseScratch 105 (by decide))
  let H : Stacks 248 A := {F with R := (Function.update (Function.update (Function.update F.R 138 []) 139 []) 140 [])}
  have hfactorFrame (i : Fin 248) (hi : 168 ≤ i.val) (hi' : i.val < 242) (hn : i ≠ 238) :
      H.R i = G.R i := by
    have h138 : i ≠ 138 := by intro he; subst i; omega
    have h139 : i ≠ 139 := by intro he; subst i; omega
    have h140 : i ≠ 140 := by intro he; subst i; omega
    simpa only [H,Function.update_of_ne h138,Function.update_of_ne h139,Function.update_of_ne h140]
      using hfactors i hi hi' hn
  have hW' : (H.R 204).length = 12*band+1 := hreadyRecovery.m2n
  have hN' : (H.R 206).length = B.card := hreadyRecovery.sn
  have hw' : (H.R 174).length = w := hreadyRecovery.ready.wn
  have htable' : H.R 220 = bandTableWords A w B (12*band+1) columns 0++S.R 220 := by
    rw [hfactorFrame 220 (by decide) (by decide) (by decide)]
    simpa [G,extendStacks] using hrawTable
  have hscratch' : ∀ i ∈ ([104,105,106,107,108,109,111,112] : List (Fin 248)), H.R i = [] := by
    intro i hi
    have hn : i ≠ 138 ∧ i ≠ 139 ∧ i ≠ 140 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [H,Function.update_of_ne hn.1,Function.update_of_ne hn.2.1,Function.update_of_ne hn.2.2]
      using hreleaseScratch i hi
  obtain ⟨v₅,n₄,hu₅,hn₄,he₅⟩ := packedTableRelease_exec (body := body') B (12*band+1) w columns hlen
    (S.R 220) v₄ H hW' hN' hw' htable' hscratch'
  let J : Stacks 248 A := {H with R := Function.update H.R 220 (S.R 220)}
  have hstockJ : ∀ i ∈ packedFactorOwnedIndices,
      (J.R (packedFactorOwnedReg i)).length ≤ boundaryFactorStockBound q w band B.card := by
    intro i hi
    have hb := packedFactorOwnedReg_bounds i hi
    have himem : 154 ≤ i.val ∧ i ≠ 206 := by simpa [packedFactorOwnedIndices] using hi
    have hframeJ : J.R (packedFactorOwnedReg i) = G.R (packedFactorOwnedReg i) := by
      rw [show J.R (packedFactorOwnedReg i) = H.R (packedFactorOwnedReg i) from
        Function.update_of_ne hb.2.2 _ _]
      exact hfactorFrame _ hb.1 (by omega) (by intro he; have hh := congrArg Fin.val he; omega)
    rw [hframeJ]
    have he : (packedBoundaryFactorReg (preparedBoundaryCoreReg i)).val < 242 := by
      change (packedFactorOwnedReg i).val < 242
      omega
    simpa only [G,packedFactorOwnedReg,extendStacks,Fin.val_castLE,dite_eq_left he,
      embStk,Function.comp_apply] using hstock i himem.1 himem.2
  obtain ⟨v₆,n₅,hu₆,hn₅,he₆⟩ := packedFactorRelease_exec (body := body')
    (boundaryFactorStockBound q w band B.card) v₅ J hstockJ
  let K := packedFactorReleased J
  have hkeep (i : Fin 248) (hi : i.val < 168 ∨ 238 ≤ i.val ∨ i = 220) : K.R i = J.R i := by
    apply packedFactorReleased_off
    intro hm
    have hb := packedFactorOwnedRegs_bounds i hm
    rcases hi with hi | hi | rfl <;> omega
  have hheaders₁ : PackedHaloRetainedHeaders (2^15*p)
      (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
      q l s t u band a b V w (embStk packedHaloRuntimeReg F₁) :=
    ⟨hheaders,hmeta,hstageMaster,hlevel⟩
  have hretainedHeaders : PackedHaloRetainedHeaders (2^15*p)
      (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
      q l s t u band a b V w (embStk packedRecoveryRuntimeReg K) := by
    apply hheaders₁.of_frame
    intro i hi
    have hs := haloRetainedHeaderPorts_safe i hi
    have h138 : packedRecoveryRuntimeReg i ≠ 138 := by
      intro he; apply hs.2.2.1; apply Fin.ext; exact congrArg (fun k : Fin 248 => k.val) he
    have h139 : packedRecoveryRuntimeReg i ≠ 139 := by
      intro he; apply hs.2.2.2.1; apply Fin.ext; exact congrArg (fun k : Fin 248 => k.val) he
    have h140 : packedRecoveryRuntimeReg i ≠ 140 := by
      intro he; apply hs.2.2.2.2.1; apply Fin.ext; exact congrArg (fun k : Fin 248 => k.val) he
    have h220 : packedRecoveryRuntimeReg i ≠ 220 := by
      intro he
      have hv := congrArg (fun k : Fin 248 => k.val) he
      have hi := i.isLt
      change i.val = 220 at hv
      omega
    change K.R (packedRecoveryRuntimeReg i) = F₁.R (packedHaloRuntimeReg i)
    rw [hkeep _ (Or.inl i.isLt)]
    simp only [J,H,Function.update_of_ne h220,Function.update_of_ne h138,
      Function.update_of_ne h139,Function.update_of_ne h140]
    have hr := hretained (packedRecoveryRuntimeReg i) (haloRetainedHeaderPorts_mem i hi)
    exact hr.trans (by
      simp [G,extendStacks,packedRecoveryRuntimeReg,packedHaloRuntimeReg,
        show i.val < 242 by have hi := i.isLt; omega])
  refine ⟨v₆,K,n₁+(n₂+(n₃+(n₄+n₅))),D,
    hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))),?_,
    Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅ he₆))),
    hin.trans hinputFrame,hout.trans houtputFrame,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,hfits,?_,?_,hretainedHeaders,?_⟩
  · exact (Nat.add_le_add hn₁ (Nat.add_le_add hn₂ (Nat.add_le_add hn₃ (Nat.add_le_add hn₄ hn₅)))).trans (by
      dsimp only [packedHaloSolveUsingCost,page,band,B,bits,q,w,targetB]
      omega)
  · rw [hkeep 93 (by decide)]
    simpa [J,H] using h93'.trans (by simpa [G,extendStacks] using h93)
  · rw [hkeep 238 (by decide)]; simpa [J,H] using h238
  · rw [hkeep 138 (by decide)]; simp [J,H]
  · rw [hkeep 139 (by decide)]; simp [J,H]
  · rw [hkeep 140 (by decide)]; simp [J,H]
  · rw [hkeep 220 (by decide)]; simp [J]
  · intro i hi; simp [K,packedFactorReleased,hi]
  · rw [hkeep 130 (by decide)]; simpa [J,H,w,bits,B,band,targetB] using hwidth'
  · rw [hkeep 104 (by decide)]; simpa [J,H] using hreleaseScratch 104 (by decide)
  · rw [hkeep 105 (by decide)]; simpa [J,H] using hreleaseScratch 105 (by decide)
  · rw [hkeep 109 (by decide)]; simpa [J,H] using hreleaseScratch 109 (by decide)
  · rw [hkeep 132 (by decide)]; simpa [J,H] using houtput'
  · simpa only [hkeep 132 (by decide),show J.R 132 = F.R 132 by simp [J,H]] using haccuracy


  · intro i hi93 hi110
    let j : Fin 248 := ⟨i.val,by have hi := i.isLt; omega⟩
    have hj : j.val < 117 := i.isLt
    have h138 : j ≠ 138 := by
      intro he
      have hv := congrArg (fun k : Fin 248 => k.val) he
      change i.val = 138 at hv
      have hi := i.isLt
      omega
    have h139 : j ≠ 139 := by
      intro he
      have hv := congrArg (fun k : Fin 248 => k.val) he
      change i.val = 139 at hv
      have hi := i.isLt
      omega
    have h140 : j ≠ 140 := by
      intro he
      have hv := congrArg (fun k : Fin 248 => k.val) he
      change i.val = 140 at hv
      have hi := i.isLt
      omega
    have h220 : j ≠ 220 := by
      intro he
      have hv := congrArg (fun k : Fin 248 => k.val) he
      change i.val = 220 at hv
      have hi := i.isLt
      omega
    change K.R j = []
    rw [hkeep j (Or.inl (by omega))]
    simp only [J,H,Function.update_of_ne h220,Function.update_of_ne h138,
      Function.update_of_ne h139,Function.update_of_ne h140]
    exact hnativeRecovery i hi93 hi110

  · obtain ⟨residual,hlen,hs⟩ := hbuffers
    refine ⟨residual,hlen,?_⟩
    rw [hkeep 110 (by decide)]
    simpa [J,H] using hs

theorem packedHaloSolve_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hbody : ∀ f, body' f = embProg packedBoundaryRecoveryBase id (body f))
    {p l s t u target rhsExp a b V : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (C : ZMod s → GaussianInt) (tail E outputTail : List (Fin (A+4)))
    (v : HS 248 Q A U) (S : Stacks 242 A)
    (h109 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 109 = []) (h115 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 115 = []) (h116 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 116 = [])
    (hleft : ∀ i : Fin 224, (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).L (preparedBoundaryCoreReg i) = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u
      (boundaryTableBits p (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u
        (boundaryTableBits p (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)
      l s t u (PhaseCellBand.width p u) 0 0 (cstream A (executionWidth p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) (packedInterval a (b-a) C)++tail)
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
    (h239 : S.R 239 = [])
    (hab : a ≤ b) (haLt : a < s) (hsep : b-a+PhaseCellBand.width p u ≤ s)
    (hwide : 8*(t+1)^2+4*PhaseCellBand.width p u+8 < 2^V)
    (hVeq : V = weightWorkspaceWidth (2^15*p) (executionPrecision p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) (2*(executionPrecision p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp)+8) t u)
    (hwV : (executionWidth p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) < 2^V) (hcoords : b < 2^V) (hunits : b*(executionWidth p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) < 2^V)
    (hC : ∀ k, ‖value (executionPrecision p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (h157 : (S.R 157).length ≤ V) (h158 : S.R 158 = []) (h167 : S.R 167 = [])
    (houtput : S.R 132 = E++outputTail) (hE : E.length = (b-a)*(executionWidth p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp))
    (hfresh : ∀ k ∈ [(125 : Fin 168),127,130,133,138,129,131,134,135,136,140,153,166],
      (embStk packedHaloRuntimeReg S).R k = [])
    (hrange : EncodedRange A (executionWidth p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) (executionPrecision p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp)
      (interiorOutputExponent p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) E)
    (hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))))
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x
      (fun k => (value (executionPrecision p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) (C k)).re)) :
    let band := PhaseCellBand.width p u
    let B := haloBoundary s t band a b
    let bits := boundaryTableBits p (boundaryRecoveryTarget p target) rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    ∃ v' F n, ∃ D : ZMod s → GaussianInt,
      v'.user = v.user ∧
      n ≤ packedHaloSolveCost p u l target rhsExp s t a b V ∧
      Exec body' (packedHaloSolve hR hQ) (mk v (extendStacks (by decide) S)) n (mk v' F) ∧
      F.inp = S.inp ∧ F.out = S.out ∧
      F.R 93 = S.R 93 ∧ F.R 238 = S.R 238 ∧
      F.R 138 = [] ∧ F.R 139 = [] ∧ F.R 140 = [] ∧ F.R 220 = S.R 220 ∧
      (∀ i ∈ packedFactorOwnedRegs, F.R i = []) ∧
      (F.R 130).length = w ∧ F.R 104 = [] ∧ F.R 105 = [] ∧ F.R 109 = [] ∧
      F.R 132 = cstream A w (packedInterval a (b-a) D)++outputTail ∧
      (∀ i, Fits w (D i)) ∧
      PhaseCellInterface.ErrorOn (haloVertices s a b)
        (fun i => (packedIntervalRead q w a (F.R 132) i).re) x (1/(2 : ℝ)^target) ∧
      PackedHaloNativeClean (embStk packedRecoveryRuntimeReg F) ∧
      PackedHaloRetainedHeaders (2^15*p)
        (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
        q l s t u band a b V w (embStk packedRecoveryRuntimeReg F) ∧
      ∃ residual : List (Fin (A+4)), residual.length = (b-a)*w ∧
        F.R 110 = residual++(cstream A w (packedInterval a (b-a) C)++tail) := by
  exact packedHaloSolveUsing_spec (body := body) (body' := body') true
    hR hQ hA hbody hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad
    C tail E outputTail v S h109 h115 h116 hleft hready haMaster hbMaster h0 h139 h127 h138
    h143 h147 h151 h153 h152 hnew h132left hV h155 h165 hfitV hgeometryBlank h239
    hab haLt hsep hwide hVeq hwV hcoords hunits hC h157 h158 h167 houtput hE hfresh hrange hdom x hx

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
