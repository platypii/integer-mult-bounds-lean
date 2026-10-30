module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloPreparedBoundaryExtended
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryRecoveryBuffers

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloPreparedBoundary
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryRecoveryUnfold

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 242 Q A U} {body' : P → Pr P 248 Q A U}

theorem packedHaloPreparedRecovery_exec (hbody : ∀ f, body' f = embProg packedBoundaryRecoveryBase id (body f))
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l s t p u target finalTarget rhsExp a b V boundaryTarget : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hα : 0 < α) (hwidth : 8*p ≤ 2^u) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (hab : a ≤ b) (hb : b ≤ s) (hband : PhaseCellBand.width p u ≤ s)
    (hwide : 8*(t+1)^2+4*PhaseCellBand.width p u+8 < 2^V)
    (hVeq : V = weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (2*executionPrecision p l target rhsExp+8) t u)
    (hwV : executionWidth p l target rhsExp < 2^V)
    (hcoords : b < 2^V) (hunits : b*executionWidth p l target rhsExp < 2^V)
    (tail E outputTail : List (Fin (A+4)))
    (v : HS 248 Q A U) (S : Stacks 242 A)
    (hnative : embStk packedCellCoreReg (embStk packedHaloRuntimeReg S) = releasedCellBank []
      (cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) C)++tail) ((embStk packedHaloRuntimeReg S).R 93) (embStk packedHaloRuntimeReg S).inp (embStk packedHaloRuntimeReg S).out)
    (hmasters : ∀ r ∈ groupHeaderCopies, ((embStk packedHaloRuntimeReg S).R (packedHeaderReg r.1)).length =
      groupHeaderValue (2^15*p) (executionStagePrecision p l target rhsExp+1)
        (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) 0 r.1)
    (ha : ((embStk packedHaloRuntimeReg S).R 141).length = a) (hb' : ((embStk packedHaloRuntimeReg S).R 142).length = b)
    (hmeta : CouplingIntervalMetadata V s t (PhaseCellBand.width p u) a b a (b-a) (embStk packedHaloRuntimeReg S))
    (h157 : ((embStk packedHaloRuntimeReg S).R 157).length ≤ V)
    (houtput : (embStk packedHaloRuntimeReg S).R 132 = E++outputTail) (hE : E.length = (b-a)*executionWidth p l target rhsExp)
    (hfresh : ∀ k ∈ [(125 : Fin 168),127,130,133,138,129,131,134,135,136,140,153,166], (embStk packedHaloRuntimeReg S).R k = [])
    (haLt : a < s) (hfitV : a+((b-a)+2*PhaseCellBand.width p u)+s < 2^V)
    (h139 : (embStk packedHaloRuntimeReg S).R 139 = []) (h143 : (embStk packedHaloRuntimeReg S).R 143 = [])
    (hleft : ∀ k ∈ [(121 : Fin 168),122,123,124], (embStk packedHaloRuntimeReg S).L k = [])
    (hsep : b-a+PhaseCellBand.width p u ≤ s) (h158 : (embStk packedHaloRuntimeReg S).R 158 = []) (h167 : (embStk packedHaloRuntimeReg S).R 167 = [])
    (hrange : EncodedRange A (executionWidth p l target rhsExp) (executionPrecision p l target rhsExp)
      (interiorOutputExponent p l target rhsExp) E)
    (hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))))
    (hq : executionPrecision p l target rhsExp = executionPrecision p l
      (initialSchurTarget p u (boundaryTableBits p boundaryTarget rhsExp
        (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)
 :
    let band := PhaseCellBand.width p u
    let B := haloBoundary s t band a b
    let bits := boundaryTableBits p boundaryTarget rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let W := 12*PhaseCellBand.width p u+1
    ∀ columns : List (ZMod s → GaussianInt),
    PreparedBoundaryColumns A p bits q w W B columns →
    target = boundaryHaloTarget p u boundaryTarget rhsExp B.card →
    (∀ i ∈ B, ∀ j ∈ B, |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j-
      (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
        (haloInterior s t band a b).toList).1 i j| ≤ 1/(2 : ℝ)^bits) →
    PackedPreparedBank q w W B.card S →
    let AZ := factorRankIntegerMatrix B W columns
    let K := factorNewtonSteps p q
    let Lc := naturalLineLc q K W B.card AZ
    let Uc := naturalLineUc q K W B.card AZ
    let rcs := naturalLineRcs q K W B.card AZ
    PackedBoundaryFactorPages (cstream A w (Lc.map colC).flatten)
      (cstream A w (Uc.map colC).flatten)
      (cstream A w (rcs.map fun z => (⟨z,0⟩ : GaussianInt))) S →
    boundaryTarget = boundaryRecoveryTarget p finalTarget →
    ∀ y : ZMod s → ℝ,
    SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) y
      (fun k => (value q (C k)).re) →
    (∀ j < b-a, ∀ z ∈ couplingCoefficientWords (2^15*p) q s t u band (a+j), Fits w z ∧ z.im = 0) →
    ∃ v' F n, ∃ D : ZMod s → GaussianInt,
      v'.user = v.user ∧
      n ≤ packedHaloPreparedBoundaryCost p u l target boundaryTarget rhsExp s t a b V+
        packedBoundaryRecoveryCost p u l finalTarget rhsExp s t a b V q w ∧
      Exec body' (.seq (embProg packedBoundaryRecoveryBase id (packedHaloPreparedBoundary hR hQ))
        (packedBoundaryRecovery hR hQ)) (mk v (extendStacks (by decide) S)) n (mk v' F) ∧
      F.R 132 = cstream A w (packedInterval a (b-a) D)++outputTail ∧
      PhaseCellInterface.ErrorOn (haloVertices s a b)
        (fun i => (packedIntervalRead q w a (F.R 132) i).re) y (1/(2 : ℝ)^finalTarget) ∧
      PackedPreparedBank q w W B.card (embStk packedBoundaryRecoveryBase F) := by
  dsimp only
  intro columns hcolumns hcell htable hbank hpages hboundary y hy hcoeff
  let band := PhaseCellBand.width p u
  let B := haloBoundary s t band a b
  let bits := boundaryTableBits p boundaryTarget rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let W := 12*band+1
  obtain ⟨xI,hxI,v₁,T,n₁,D₁,hu₁,hn₁,he₁,hbankFinal,hdata,hpagesFinal,hleftFinal,hframe,haccuracy,hheaders,hstage,hlevel,hnativeFinal,hcleanFinal,hgeometryFinal,hsolutionTail,hbuffers,hprivate⟩ :=
    packedHaloPreparedBoundary_extended_exec (body := body) (body' := body') hbody hR hQ hA hp hα hwidth hst hu hαu hθ hgap
      hbudget hpad C hC hab hb hband hwide hVeq hwV hcoords hunits tail E outputTail
      v S hnative hmasters ha hb' hmeta h157 houtput hE hfresh haLt hfitV h139 h143 hleft
      hsep h158 h167 hrange hdom hq columns hcolumns hcell htable hbank hpages
  let AZ := factorRankIntegerMatrix B W columns
  let K := factorNewtonSteps p q
  let rows := (bFoldOrder s B).map (fun i => realPartWord
    (couplingRowField (2^15*p) q t u band a b false D₁ C i))
  let ys := (bandSolveVec q W (naturalLineLc q K W B.card AZ) (naturalLineUc q K W B.card AZ)
    (naturalLineRcs q K W B.card AZ) (rows.map (normalizeBoundaryWord q (q/2-1)))).map (unscaleBoundaryWord q)
  let F₁ : Stacks 242 A := {T with R := Function.update (Function.update T.R 143 []) 238 (cstream A w ys++T.R 238)}
  let G := extendStacks (by decide : 242 ≤ 248) F₁
  change PackedPreparedBank q w W B.card F₁ at hbankFinal
  change PackedHaloRecoveryBuffers p s t u a b q w C D₁ tail outputTail F₁ at hbuffers
  change CouplingMasterHeaders (2^15*p) q w s t u band a b (embStk packedHaloRuntimeReg F₁) at hheaders
  change CouplingIntervalMetadata V s t band a b a (b-a) (embStk packedHaloRuntimeReg F₁) at hgeometryFinal
  change (F₁.R 118).length = executionStagePrecision p l target rhsExp+1 at hstage
  change (F₁.R 120).length = l at hlevel
  change (∀ i : Fin 117, i ≠ 93 → i ≠ 110 → i ≠ 116 → F₁.R ⟨i.val,by omega⟩ = []) at hnativeFinal
  change (∀ k ∈ ([127,129,131,133,134,135,136,153,158,166] : List (Fin 242)), F₁.R k = []) at hcleanFinal
  change ys.length = B.card ∧ (∀ z ∈ ys, Fits w z) ∧
    (∀ y : ZMod s → ℝ, SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) y
      (fun k => (value q (C k)).re) → ∀ i < B.card,
      ‖value q (ys.getD i 0)-(y (bFoldAt s B i) : ℂ)‖ ≤ 3/(2 : ℝ)^boundaryTarget ∧
      ‖value q (ys.getD i 0)‖ ≤ (2 : ℝ)^stableInteriorExponent p rhsExp) at haccuracy
  have hruntime : embStk packedRecoveryRuntimeReg G = embStk packedHaloRuntimeReg F₁ := by
    refine Stacks.ext rfl rfl ?_ ?_
    all_goals
      funext i
      simp [G,embStk,extendStacks,packedRecoveryRuntimeReg,packedHaloRuntimeReg,
        show i.val < 242 by have hi := i.isLt; omega]
  have hw : executionWidth p l target rhsExp = w := by
    have he := hq; unfold executionPrecision at he
    dsimp [w,q,bits,B,band,executionWidth]; omega
  obtain ⟨hqs,hstages,hws⟩ := boundaryHaloTarget_sizing p u l boundaryTarget rhsExp B.card
  have hstage' : (G.R 118).length = executionStagePrecision p l (initialSchurTarget p u
      (boundaryTableBits p (boundaryRecoveryTarget p finalTarget) rhsExp B.card) 2) 2+1 := by
    have hh := hstage
    change target = boundaryHaloTarget p u boundaryTarget rhsExp B.card at hcell
    rw [hcell,hstages] at hh
    change (F₁.R 118).length = _
    simpa only [hboundary] using hh
  obtain ⟨v₂,F,n₂,D,hu₂,hn₂,he₂,h93,h139',h238,hi,ho,hout,hfits,herror,hsource,hnative₂,hleft₂,hretained,hwork₂,hready₂,hprivate₂,hfactors,hpages₂⟩ :=
    packedBoundaryRecovery_buffers_spec (body := body') (q := q) (w := w) (W := W) hR hQ hA hp hu hwidth hα hst hαu hθ hgap hbudget hdom
      hab hb hband hsep hpad (by simp only [q,bits,B,band,hboundary]) (by simp only [w,bits,B,band,hboundary]) C ys y
      (by simpa only [hq] using hC) haccuracy.1 haccuracy.2.1
      (by simpa only [hboundary] using haccuracy.2.2 y hy) hy D₁ (S.R 238) outputTail tail v₁ G
      (by simpa [G,packedBoundaryRecoveryBase] using hbankFinal)
      (by simpa [G,packedBoundaryRecoveryBase] using hbuffers)
      (by simp [G,extendStacks,F₁])
      (by simpa [G,extendStacks,F₁,hsolutionTail] using (rfl : cstream A w ys++T.R 238 = cstream A w ys++T.R 238))
      (by change (embStk packedHaloRuntimeReg F₁).R 165 = _; exact hgeometryFinal.count)
      (fun i hi => (extendStacks_fresh (by decide) F₁ i hi).1)
      (fun i hi => (extendStacks_fresh (by decide) F₁ i hi).2)
      (by rw [hruntime]; exact hheaders)
      hstage' (by simpa [G,extendStacks] using hlevel)
      (by intro i hi93 hi110 hi116; have hi : i.val < 242 := by have hh := i.isLt; omega
          simpa only [G,extendStacks,dite_eq_left hi] using hnativeFinal i hi93 hi110 hi116)
      (by
        intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · simpa [G,extendStacks] using hcleanFinal 127 (by decide)
        · simpa [G,extendStacks] using hcleanFinal 129 (by decide)
        · simpa [G,extendStacks] using hcleanFinal 131 (by decide)
        · simpa [G,extendStacks] using hcleanFinal 133 (by decide)
        · simpa [G,extendStacks] using hcleanFinal 134 (by decide)
        · simpa [G,extendStacks] using hcleanFinal 135 (by decide)
        · simpa [G,extendStacks] using hcleanFinal 136 (by decide)
        · simpa [G,extendStacks] using hcleanFinal 153 (by decide)
        · simpa [G,extendStacks] using hcleanFinal 158 (by decide)
        · simpa [G,extendStacks] using hcleanFinal 166 (by decide))
      hcoeff hwide hfitV (by simpa only [hq] using hVeq)
      (by simpa only [hw] using hwV) hcoords (by simpa only [hw] using hunits)
      (by rw [hruntime]; exact hgeometryFinal)
  exact ⟨v₂,F,n₁+n₂,D,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂,hout,herror,⟨hready₂,hwork₂⟩⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
