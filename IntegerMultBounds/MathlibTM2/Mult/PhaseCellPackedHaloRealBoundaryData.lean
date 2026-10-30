module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreservePackedRhs

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloBoundaryData
public import IntegerMultBounds.MathlibTM2.Host.MapOwnedLine
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloResidualNormalization
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedReleasedCellBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedSharedLocalFeedCouplingInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingCoefficientAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedCouplingCoefficientInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializePackedHaloKeys
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloGroupAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellKeyedPackedHaloInput

/-! Project the actual folded halo residual to real words and establish the
magnitude contract consumed by boundary normalization. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

noncomputable def packedHaloRealBoundaryData (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 168 Q A U :=
  .seq (packedHaloBoundaryData hR hQ) (mapOwnedLine 143 0 realPartSymbol)

def packedHaloRealBoundaryDataCost (p l s t u target rhsExp a b V : ℕ) [NeZero s] : ℕ :=
  packedHaloBoundaryDataCost p l s t u target rhsExp a b V+
    4*(haloBoundary s t (PhaseCellBand.width p u) a b).card*executionWidth p l target rhsExp+4

theorem packedHaloRealBoundaryData_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hnative : embStk packedCellCoreReg S = releasedCellBank []
      (cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) C)++tail) (S.R 93) S.inp S.out)
    (hmasters : ∀ r ∈ groupHeaderCopies, (S.R (packedHeaderReg r.1)).length =
      groupHeaderValue (2^15*p) (executionStagePrecision p l target rhsExp+1)
        (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) 0 r.1)
    (ha : (S.R 141).length = a) (hb' : (S.R 142).length = b)
    (hmeta : CouplingIntervalMetadata V s t (PhaseCellBand.width p u) a b a (b-a) S)
    (h157 : (S.R 157).length ≤ V)
    (houtput : S.R 132 = E++outputTail) (hE : E.length = (b-a)*executionWidth p l target rhsExp)
    (hfresh : ∀ k ∈ [(125 : Fin 168),127,130,133,138,129,131,134,135,136,140,153,166], S.R k = [])
    (haLt : a < s) (hfitV : a+((b-a)+2*PhaseCellBand.width p u)+s < 2^V)
    (h139 : S.R 139 = []) (h143 : S.R 143 = [])
    (hleft : ∀ k ∈ [(121 : Fin 168),122,123,124], S.L k = [])
    (hsep : b-a+PhaseCellBand.width p u ≤ s) (h158 : S.R 158 = []) (h167 : S.R 167 = [])
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
      Exec body (packedHaloRealBoundaryData hR hQ) (mk v S) m (mk v' F) ∧
      F.R 93 = S.R 93 ∧ F.R 143 = folded ∧ F.R 116 = List.replicate B.card tick ∧
      F.R 167 = couplingSourceIntervalMaskSymbols true A s t band a b a (b-a) ∧
      F.R 110 = Z++(cstream A w (packedInterval a (b-a) C)++tail) ∧
      F.R 132 = cstream A w (packedInterval a (b-a) D)++outputTail ∧
      embStk packedCellCoreReg F = countedReleasedCellBank B.card Z
        (cstream A w (packedInterval a (b-a) C)++tail) (S.R 93) S.inp S.out ∧
      (∀ k, ‖value q (D k)‖ ≤ (2 : ℝ)^interiorOutputExponent p l target rhsExp) ∧
      (∀ k, Fits w (D k)) ∧ (F.R 130).length = w ∧
      F.R 138 = cstream A w (couplingCoefficientPageInterval (2^15*p) q s t u band a b a (b-a)) ∧
      F.R 139 = List.replicate (couplingCoefficientPageInterval (2^15*p) q s t u band a b a (b-a)).length tick ∧
      F.R 140 = List.replicate (2*band+1) tick ∧
      CouplingIntervalMetadata V s t band a b a (b-a) F ∧ F.R 126 = S.R 126 ∧ F.R 127 = [] ∧ F.R 135 = [] ∧
      (∀ k : Fin 168, 117 ≤ k.val → k ∉ packedHaloInteriorPagePorts → k ≠ 167 → F.L k = S.L k ∧ F.R k = S.R k) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t band a b)
        (fun k => (value q (D k)).re) x (1/(2 : ℝ)^target) ∧
      (∀ z ∈ rows,
        (|gv q z.re| ≤ (2 : ℝ)^(q/2) ∧ |gv q z.im| ≤ (2 : ℝ)^(q/2)) ∧
        (|gv q (normalizeBoundaryWord q (q/2-1) z).re| ≤ 1/2 ∧
          |gv q (normalizeBoundaryWord q (q/2-1) z).im| ≤ 1/2)) ∧ F.L = S.L ∧ F.R 125 = [] ∧ F.R 128 = [] ∧ (F.R 157).length ≤ V := by
  dsimp only
  obtain ⟨v₁,G,m₁,D,hu₁,hm₁,he₁,h93,hfold,h116,hmask,h110,h132,hproj,hDnorm,hDfits,hw,hpage,hcount,hrows,hgeometry,hqueue,hzero,h135,hframe,herror,hleftAll,hkeys⟩ :=
    packedHaloBoundaryData_exec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget hpad C hC
      hab hb hband hwide hVeq hwV hcoords hunits tail E outputTail v S hnative hmasters ha hb'
      hmeta h157 houtput hE hfresh haLt hfitV h139 h143 hleft hsep h158 h167 hrange x hx
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let band := PhaseCellBand.width p u
  let B := haloBoundary s t band a b
  let rows := (bFoldOrder s B).map (fun i => realPartWord (couplingRowField (2^15*p) q t u band a b false D C i))
  have h0 : G.R 0 = [] := by
    simpa [embStk,packedCellCoreReg,countedReleasedCellBank,releasedCellBank] using
      congrArg (fun X : Stacks 117 A => X.R 0) hproj
  obtain ⟨v₂,hu₂,he₂⟩ := mapOwnedLine_exec (body := body) 143 0 (by decide) realPartSymbol v₁ G h0
  let F : Stacks 168 A := {G with R := Function.update G.R 143 (cstream A w rows)}
  have he₂' : Exec body (mapOwnedLine 143 0 realPartSymbol) (mk v₁ G)
      (4*B.card*w+4) (mk v₂ F) := by
    simpa only [F,rows,q,w,band,B,hfold,realPartSymbol_cstream (by omega : 4 ≤ A),
      List.map_map,Function.comp_def,length_cstream,List.length_map,bFoldOrder_length,Nat.mul_assoc] using he₂
  have hprojF : embStk packedCellCoreReg F = embStk packedCellCoreReg G := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    have hn : packedCellCoreReg k ≠ 143 := by
      intro he; have hv := congrArg (fun i : Fin 168 => i.val) he
      change k.val = 143 at hv
      have hk := k.isLt
      omega
    simp only [F,embStk_R,Function.update_of_ne hn]
  have hgeometryF : CouplingIntervalMetadata V s t band a b a (b-a) F := by
    constructor
    · simpa [F] using hgeometry.width
    · intro k hk
      have hn : k ≠ 143 := by
        simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simpa [F,hn] using hgeometry.encoded k hk
  refine ⟨v₂,F,m₁+(4*B.card*w+4),D,hu₂.trans hu₁,?_,Exec.seq he₁ he₂',?_,?_,?_,?_,?_,?_,?_,
    hDnorm,hDfits,?_,?_,?_,?_,hgeometryF,?_,?_,?_,?_,herror,?_,hleftAll,by simpa [F] using hkeys⟩
  · dsimp only [packedHaloRealBoundaryDataCost,B,band,w]
    omega
  · simpa [F] using h93
  · simp [F,rows,B,band,q,w]
  · simpa [F] using h116
  · simpa [F] using hmask
  · simpa [F] using h110
  · simpa [F] using h132
  · rw [hprojF]; exact hproj
  · simpa [F] using hw
  · simpa [F] using hpage
  · simpa [F] using hcount
  · simpa [F] using hrows
  · simpa [F] using hqueue
  · simpa [F] using hzero
  · simpa [F] using h135
  · intro k hk hn h167k
    have h143k : k ≠ 143 := by intro he; subst k; exact hn (by decide)
    simpa [F,h143k] using hframe k hk hn h167k
  · intro z hz
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hz
    exact haloResidual_normalization_bound hp hst hαu hθ hgap hbudget a b l boundaryTarget hq hdom C D hC x hx herror i

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
