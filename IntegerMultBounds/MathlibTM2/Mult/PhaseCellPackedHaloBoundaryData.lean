module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreservePackedRhs

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloResidual
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedReleasedCellBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedSharedLocalFeedCouplingInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingCoefficientAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedCouplingCoefficientInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializePackedHaloKeys
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloGroupAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellKeyedPackedHaloInput

/-! Execute every halo interior class through solver-order boundary RHS data.
The boundary mask and actual count are produced by the same execution. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

noncomputable def packedHaloBoundaryData (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 168 Q A U :=
  .seq (packedHaloResidual hR hQ) packedBoundaryData

def packedHaloBoundaryDataCost (p l s t u target rhsExp a b V : ℕ) [NeZero s] : ℕ :=
  packedHaloResidualCost p l s t u target rhsExp a b V+
    packedBoundaryDataCost V (b-a) (haloBoundary s t (PhaseCellBand.width p u) a b).card
      (executionWidth p l target rhsExp)

theorem packedHaloBoundaryData_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l s t p u target rhsExp a b V : ℕ} [NeZero s] {α d : ℝ}
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
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re)) :
    ∃ v' F m, ∃ D : ZMod s → GaussianInt,
      let q := executionPrecision p l target rhsExp
      let w := executionWidth p l target rhsExp
      let band := PhaseCellBand.width p u
      let B := haloBoundary s t band a b
      let Z := cstream A w (packedInterval a (b-a) (guardedCouplingRowField (2^15*p) q t u band a b false D C))
      let folded := cstream A w ((bFoldOrder s B).map (couplingRowField (2^15*p) q t u band a b false D C))
      v'.user = v.user ∧ m ≤ packedHaloBoundaryDataCost p l s t u target rhsExp a b V ∧
      Exec body (packedHaloBoundaryData hR hQ) (mk v S) m (mk v' F) ∧
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
        (fun k => (value q (D k)).re) x (1/(2 : ℝ)^target) ∧ F.L = S.L := by
  dsimp only
  obtain ⟨v₁,G,m₁,D,hu₁,hm₁,he₁,h93,h110,h132,hproj,hDnorm,hDfits,hw,hpage,hcount,hrows,hgeometry,h143,hqueue,hzero,h135,hframe,herror,hleftAll⟩ :=
    packedHaloResidual_exec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget hpad C hC
      hab hb hband hwide hVeq hwV hcoords hunits tail E outputTail v S hnative hmasters ha hb'
      hmeta h157 houtput hE hfresh haLt hfitV h139 h143 hleft hsep h158 h167 hrange x hx
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let band := PhaseCellBand.width p u
  let B := haloBoundary s t band a b
  let Z := cstream A w (packedInterval a (b-a) (guardedCouplingRowField (2^15*p) q t u band a b false D C))
  let folded := cstream A w ((bFoldOrder s B).map (couplingRowField (2^15*p) q t u band a b false D C))
  have hblank : ∀ k : Fin 168, k.val < 77 → G.R k = [] := by
    intro k hk
    let i : Fin 117 := ⟨k.val,by omega⟩
    have hi : packedCellCoreReg i = k := Fin.ext rfl
    have hn93 : i.val ≠ 93 := by dsimp [i]; omega
    have hn110 : i.val ≠ 110 := by dsimp [i]; omega
    have hh := congrArg (fun X : Stacks 117 A => X.R i) hproj
    simpa only [embStk,Function.comp_apply,hi,releasedCellBank,ite_eq_right hn93,ite_eq_right hn110] using hh
  have h116 : G.R 116 = [] := by
    simpa [embStk,packedCellCoreReg,releasedCellBank] using congrArg (fun X : Stacks 117 A => X.R 116) hproj
  have h167G : G.R 167 = [] := by
    rw [(hframe 167 (by decide) (by decide)).2]; exact h167
  have hB : ∀ i ∈ B, a ≤ i.val ∧ i.val < a+(b-a) := by
    intro i hi
    have hh := (mem_haloVertices _ _ _).mp (Finset.mem_sdiff.mp hi).1
    omega
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := packedBoundaryData_exec (body := body) v₁ G hgeometry
    (show a+(b-a) ≤ s by omega) hst (hab.trans hb) hb (by omega) (by omega) hfitV hblank hB
    (guardedCouplingRowField (2^15*p) q t u band a b false D C) w
    (cstream A w (packedInterval a (b-a) C)++tail) h110 h167G hw h116 h143
  have hfoldmap : (bFoldOrder s B).map (guardedCouplingRowField (2^15*p) q t u band a b false D C) =
      (bFoldOrder s B).map (couplingRowField (2^15*p) q t u band a b false D C) := by
    apply List.map_congr_left
    intro i hi
    have hiB : i ∈ B := by rwa [← List.mem_toFinset,bFoldOrder_toFinset] at hi
    exact guardedCouplingRowField_eq hst _ _ _ _ _ _ false hb D C i (Or.inr hiB)
  let F : Stacks 168 A := {G with R := (Function.update (Function.update (Function.update G.R
    167 (couplingSourceIntervalMaskSymbols true A s t band a b a (b-a)))
    116 (List.replicate B.card tick)) 143 folded)}
  have he₂' : Exec body packedBoundaryData (mk v₁ G) m₂ (mk v₂ F) := by
    have hh := hfoldmap
    dsimp only [B,band] at hh
    simpa only [F,folded,B,band,hh] using he₂
  have hprojF : embStk packedCellCoreReg F = countedReleasedCellBank B.card Z
      (cstream A w (packedInterval a (b-a) C)++tail) (S.R 93) S.inp S.out := by
    have hi := congrArg (fun X : Stacks 117 A => X.inp) hproj
    have ho := congrArg (fun X : Stacks 117 A => X.out) hproj
    refine Stacks.ext hi ho ?_ ?_
    · funext k
      simpa [embStk,F,countedReleasedCellBank,releasedCellBank] using
        congrArg (fun X : Stacks 117 A => X.L k) hproj
    · funext k
      have hv143 : k.val ≠ 143 := by have hk := k.isLt; omega
      have hv167 : k.val ≠ 167 := by have hk := k.isLt; omega
      by_cases h116k : k.val = 116
      · have hk : k = 116 := Fin.ext h116k
        subst k; simp [embStk,F,packedCellCoreReg,countedReleasedCellBank]
      · simpa [embStk,F,Function.update_apply,packedCellCoreReg,Fin.ext_iff,h116k,hv143,hv167,
          countedReleasedCellBank,releasedCellBank,Z,w,q,band] using
          congrArg (fun X : Stacks 117 A => X.R k) hproj
  have hgeometryF : CouplingIntervalMetadata V s t band a b a (b-a) F := by
    constructor
    · simpa [F] using hgeometry.width
    · intro k hk
      have hn : k ≠ 167 ∧ k ≠ 116 ∧ k ≠ 143 := by
        simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simpa [F,hn.1,hn.2.1,hn.2.2] using hgeometry.encoded k hk
  refine ⟨v₂,F,m₁+m₂,D,hu₂.trans hu₁,?_,Exec.seq he₁ he₂',?_,?_,?_,?_,?_,?_,hprojF,
    hDnorm,hDfits,?_,?_,?_,?_,hgeometryF,?_,?_,?_,?_,herror,hleftAll⟩
  · dsimp only [packedHaloBoundaryDataCost]
    dsimp only [B,band,w] at hm₂
    omega
  · simpa [F] using h93
  · simp [F,folded,B,q,w,band]
  · simp [F,B,band]
  · simp [F,band]
  · simpa [F] using h110
  · simpa [F] using h132
  · simpa [F] using hw
  · simpa [F] using hpage
  · simpa [F] using hcount
  · simpa [F] using hrows
  · simpa [F] using hqueue
  · simpa [F] using hzero
  · simpa [F] using h135
  · intro k hk hn h167k
    have h143k : k ≠ 143 := by intro he; subst k; exact hn (by decide)
    have h116k : k ≠ 116 := by intro he; subst k; norm_num at hk
    simpa [F,h143k,h116k,h167k] using hframe k hk hn

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
