module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloBoundaryWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloRealBoundaryData
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! Run the complete halo RHS producer beside the retained factor workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 242 Q A U}

noncomputable def placedPackedHaloRealBoundaryData (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 242 Q A U :=
  embProg packedHaloRuntimeReg Empty.elim (packedHaloRealBoundaryData hR hQ)

theorem placedPackedHaloRealBoundaryData_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l s t p u target rhsExp a b V boundaryTarget : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
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
    (v : HS 242 Q A U) (S : Stacks 242 A)
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
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re)) :
    ∃ v' F m, ∃ D : ZMod s → GaussianInt,
      let q := executionPrecision p l target rhsExp
      let w := executionWidth p l target rhsExp
      let band := PhaseCellBand.width p u
      let B := haloBoundary s t band a b
      let Z := cstream A w (packedInterval a (b-a) (guardedCouplingRowField (2^15*p) q t u band a b false D C))
      let rows := (bFoldOrder s B).map (fun i => realPartWord (couplingRowField (2^15*p) q t u band a b false D C i))
      let folded := cstream A w rows
      v'.user = v.user ∧ m ≤ packedHaloRealBoundaryDataCost p l s t u target rhsExp a b V ∧
      Exec body (placedPackedHaloRealBoundaryData hR hQ) (mk v S) m (mk v' F) ∧
      (
      (embStk packedHaloRuntimeReg F).R 93 = (embStk packedHaloRuntimeReg S).R 93 ∧ (embStk packedHaloRuntimeReg F).R 143 = folded ∧ (embStk packedHaloRuntimeReg F).R 116 = List.replicate B.card tick ∧
      (embStk packedHaloRuntimeReg F).R 167 = couplingSourceIntervalMaskSymbols true A s t band a b a (b-a) ∧
      (embStk packedHaloRuntimeReg F).R 110 = Z++(cstream A w (packedInterval a (b-a) C)++tail) ∧
      (embStk packedHaloRuntimeReg F).R 132 = cstream A w (packedInterval a (b-a) D)++outputTail ∧
      embStk packedCellCoreReg (embStk packedHaloRuntimeReg F) = countedReleasedCellBank B.card Z
        (cstream A w (packedInterval a (b-a) C)++tail) ((embStk packedHaloRuntimeReg S).R 93) (embStk packedHaloRuntimeReg S).inp (embStk packedHaloRuntimeReg S).out ∧
      (∀ k, ‖value q (D k)‖ ≤ (2 : ℝ)^interiorOutputExponent p l target rhsExp) ∧
      (∀ k, Fits w (D k)) ∧ ((embStk packedHaloRuntimeReg F).R 130).length = w ∧
      (embStk packedHaloRuntimeReg F).R 138 = cstream A w (couplingCoefficientPageInterval (2^15*p) q s t u band a b a (b-a)) ∧
      (embStk packedHaloRuntimeReg F).R 139 = List.replicate (couplingCoefficientPageInterval (2^15*p) q s t u band a b a (b-a)).length tick ∧
      (embStk packedHaloRuntimeReg F).R 140 = List.replicate (2*band+1) tick ∧
      CouplingIntervalMetadata V s t band a b a (b-a) (embStk packedHaloRuntimeReg F) ∧ (embStk packedHaloRuntimeReg F).R 126 = (embStk packedHaloRuntimeReg S).R 126 ∧ (embStk packedHaloRuntimeReg F).R 127 = [] ∧ (embStk packedHaloRuntimeReg F).R 135 = [] ∧
      (∀ k : Fin 168, 117 ≤ k.val → k ∉ packedHaloInteriorPagePorts → k ≠ 167 → (embStk packedHaloRuntimeReg F).L k = (embStk packedHaloRuntimeReg S).L k ∧ (embStk packedHaloRuntimeReg F).R k = (embStk packedHaloRuntimeReg S).R k) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t band a b)
        (fun k => (value q (D k)).re) x (1/(2 : ℝ)^target) ∧
      (∀ z ∈ rows,
        (|gv q z.re| ≤ (2 : ℝ)^(q/2) ∧ |gv q z.im| ≤ (2 : ℝ)^(q/2)) ∧
        (|gv q (normalizeBoundaryWord q (q/2-1) z).re| ≤ 1/2 ∧
          |gv q (normalizeBoundaryWord q (q/2-1) z).im| ≤ 1/2)) ∧
      (embStk packedHaloRuntimeReg F).L = (embStk packedHaloRuntimeReg S).L ∧
      (embStk packedHaloRuntimeReg F).R 125 = [] ∧ (embStk packedHaloRuntimeReg F).R 128 = [] ) ∧
      (∀ k : Fin 242, 168 ≤ k.val → F.L k = S.L k ∧ F.R k = S.R k) ∧ F.L = S.L := by
  dsimp only
  obtain ⟨v₁,T₁,m,D,hu₁,hm,he,hrest⟩ := packedHaloRealBoundaryData_exec
    (body := fun p : Empty => nomatch p) hR hQ hA hp hst hu hαu hθ hgap hbudget hpad C hC
    hab hb hband hwide hVeq hwV hcoords hunits tail E outputTail
    (embDn packedHaloRuntimeReg v) (embStk packedHaloRuntimeReg S)
    hnative hmasters ha hb' hmeta h157 houtput hE hfresh haLt hfitV h139 h143 hleft hsep h158 h167
    hrange hdom hq x hx
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    packedHaloRuntimeReg_injective (fun p => nomatch p) he v rfl S rfl
  let F := embOvr packedHaloRuntimeReg T₁.get S
  have hproj : embStk packedHaloRuntimeReg F = T₁ :=
    embStk_ovr packedHaloRuntimeReg_injective T₁ S
  rcases hrest with ⟨h93,hfold,hcount,hmask,hsource,houtput,hbank,hDnorm,hDfits,hword,
    hpage,hpageCount,hrows,hgeometry,hqueue,hzero,h135,hframe,herror,hbound,hleftAll,hkeys⟩
  refine ⟨v₂,F,m,D,hu₂.trans hu₁,hm,he₂,?_,?_,embOvr_left_of_eq S T₁ hleftAll⟩
  · rw [hproj]
    exact ⟨h93,hfold,hcount,hmask,hsource,houtput,hbank,hDnorm,hDfits,hword,
      hpage,hpageCount,hrows,hgeometry,hqueue,hzero,h135,hframe,herror,hbound,hleftAll,hkeys⟩
  · exact packedHaloRuntime_high_frame S T₁

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
