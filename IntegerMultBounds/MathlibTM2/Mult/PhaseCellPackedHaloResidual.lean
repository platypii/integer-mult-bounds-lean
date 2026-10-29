module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreservePackedRhs

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloInteriorCoefficients
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedSharedLocalFeedCouplingInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingCoefficientAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedCouplingCoefficientInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializePackedHaloKeys
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloGroupAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellKeyedPackedHaloInput

/-! Execute the complete grouped interior, coefficient setup and local residual
coupling. The borrowed RHS is restored and the residual is an owned local prefix. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

noncomputable def packedHaloResidual (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 168 Q A U :=
  .seq (packedHaloInteriorCoefficients hR hQ) (preparedSharedLocalFeedCouplingInterval hQ false)

def packedHaloResidualCost (p l s t u target rhsExp a b V : ℕ) : ℕ :=
  packedHaloInteriorCoefficientsCost p l s t u target rhsExp a b V+
    preparedSharedLocalFeedCouplingIntervalCost false (2^15*p) (executionPrecision p l target rhsExp)
      (executionWidth p l target rhsExp) s t u (PhaseCellBand.width p u) a b a (b-a) V

theorem packedHaloResidual_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
      let Z := cstream A w (packedInterval a (b-a)
        (guardedCouplingRowField (2^15*p) q t u (PhaseCellBand.width p u) a b false D C))
      v'.user = v.user ∧ m ≤ packedHaloResidualCost p l s t u target rhsExp a b V ∧
      Exec body (packedHaloResidual hR hQ) (mk v S) m (mk v' F) ∧
      F.R 93 = S.R 93 ∧
      F.R 110 = Z++(cstream A w (packedInterval a (b-a) C)++tail) ∧
      F.R 132 = cstream A w (packedInterval a (b-a) D)++outputTail ∧
      embStk packedCellCoreReg F = releasedCellBank Z
        (cstream A w (packedInterval a (b-a) C)++tail) (S.R 93) S.inp S.out ∧
      (∀ k, ‖value q (D k)‖ ≤ (2 : ℝ)^interiorOutputExponent p l target rhsExp) ∧
      (∀ k, Fits w (D k)) ∧
      (F.R 130).length = w ∧
      F.R 138 = cstream A w (couplingCoefficientPageInterval (2^15*p) q s t u (PhaseCellBand.width p u) a b a (b-a)) ∧
      F.R 139 = List.replicate (couplingCoefficientPageInterval (2^15*p) q s t u (PhaseCellBand.width p u) a b a (b-a)).length tick ∧
      F.R 140 = List.replicate (2*PhaseCellBand.width p u+1) tick ∧
      CouplingIntervalMetadata V s t (PhaseCellBand.width p u) a b a (b-a) F ∧
      F.R 143 = [] ∧ F.R 126 = S.R 126 ∧ F.R 127 = [] ∧ F.R 135 = [] ∧
      (∀ k : Fin 168, 117 ≤ k.val → k ∉ packedHaloInteriorPagePorts → F.L k = S.L k ∧ F.R k = S.R k) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t (PhaseCellBand.width p u) a b)
        (fun k => (value q (D k)).re) x (1/(2 : ℝ)^target) ∧ F.L = S.L := by
  dsimp only
  obtain ⟨v₁,G,m₁,D,hu₁,hm₁,he₁,h93,hi,ho,houtput,hDnorm,hDfits,hnativeG,hready,hgeometry,hpage,hcount,hrows,h143G,h135G,hqueue,hzero,hframe,herror,hleftAll⟩ :=
    packedHaloInteriorCoefficients_exec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget hpad C hC
      hab hb hband hwide hVeq hwV hcoords hunits tail E outputTail v S hnative hmasters ha hb'
      hmeta h157 houtput hE hfresh haLt hfitV h139 h143 hleft hrange x hx
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let band := PhaseCellBand.width p u
  let Z := cstream A w (packedInterval a (b-a) (guardedCouplingRowField (2^15*p) q t u band a b false D C))
  have hpass (k : Fin 168) (hk : 117 ≤ k.val) (hn : k ∉ packedHaloInteriorPagePorts) := (hframe k hk hn).2
  have hw5 : 5 ≤ w := by dsimp [w,executionWidth]; omega
  have hqw : q+4 ≤ w := by dsimp [q,w,executionPrecision,executionWidth]; omega
  have hwcoef : q+(8*p+1)+2 ≤ w := by
    dsimp [q,w,executionPrecision,executionWidth,executionExponent,inputExponent,sourceExponent]
    omega
  have has : ∀ j < b-a, ∀ z ∈ couplingCoefficientWords (2^15*p) q s t u band (a+j), Fits w z ∧ z.im = 0 := by
    intro j _ z hz
    have hh := couplingCoefficientWords_bounds hp (NeZero.pos s) hst hαu hθ hgap hbudget z hz
    exact ⟨fits_of_value_power hwcoef z hh.1,hh.2⟩
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := preparedSharedLocalFeedCouplingInterval_exec (body := body)
    hQ false hA hw5 hqw hst D C (show a+(b-a) ≤ s by omega)
    outputTail [] (S.R 93) (cstream A w (packedInterval a (b-a) C)++tail) v₁ G hready rfl (by omega) hsep
    houtput hzero (by simp only [hrows,List.length_replicate]) (by simpa only [List.append_nil] using hpage)
    h93 h143G hDfits has V
    (by rw [hpass 166 (by decide) (by decide)]; exact hfresh 166 (by simp))
    (by simp only [hcount,List.length_replicate,q]) (hab.trans hb) hb hband hwide hfitV hgeometry
    (by rw [hpass 158 (by decide) (by decide)]; exact h158) h135G
    (by rw [hpass 167 (by decide) (by decide)]; exact h167)
  let F : Stacks 168 A := {G with R := (Function.update (Function.update G.R 93 (S.R 93)) 110 (Z++G.R 110))}
  have h110G : G.R 110 = cstream A w (packedInterval a (b-a) C)++tail := by
    simpa [embStk,packedCellCoreReg,releasedCellBank,w] using congrArg (fun B : Stacks 117 A => B.R 110) hnativeG
  have hproj : embStk packedCellCoreReg F = releasedCellBank Z
      (cstream A w (packedInterval a (b-a) C)++tail) (S.R 93) S.inp S.out := by
    refine Stacks.ext hi ho ?_ ?_
    · funext k
      simpa [embStk,F,releasedCellBank] using congrArg (fun B : Stacks 117 A => B.L k) hnativeG
    · funext k
      by_cases h93k : k.val = 93
      · have hk : k = 93 := Fin.ext h93k
        subst k; simp [embStk,F,packedCellCoreReg,releasedCellBank]
      by_cases h110k : k.val = 110
      · have hk : k = 110 := Fin.ext h110k
        subst k; simp [embStk,F,packedCellCoreReg,releasedCellBank,h110G]
      · simpa [embStk,F,packedCellCoreReg,Function.update_apply,Fin.ext_iff,h93k,h110k,releasedCellBank]
          using congrArg (fun B : Stacks 117 A => B.R k) hnativeG
  have hgeometryF : CouplingIntervalMetadata V s t band a b a (b-a) F := by
    constructor
    · simpa [F] using hgeometry.width
    · intro k hk
      have hn : k ≠ 93 ∧ k ≠ 110 := by
        simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simpa [F,hn.1,hn.2] using hgeometry.encoded k hk
  refine ⟨v₂,F,m₁+m₂,D,hu₂.trans hu₁,?_,Exec.seq he₁ he₂,?_,?_,?_,hproj,hDnorm,hDfits,?_,?_,?_,?_,hgeometryF,?_,?_,?_,?_,?_,herror,hleftAll⟩
  · dsimp only [packedHaloResidualCost]
    dsimp only [q,w,band] at hm₂
    omega
  · simp [F]
  · simp [F,h110G,Z,q,w,band]
  · simpa [F] using houtput
  · simpa [F,embStk,sharedCouplingCoreReg,sharedCouplingReg,packedCellCoreReg] using hready.width
  · simpa [F,q,w,band] using hpage
  · simpa [F,q,w,band] using hcount
  · simpa [F,q,w,band] using hrows
  · simpa [F] using h143G
  · simpa [F] using hqueue
  · simpa [F] using hzero
  · simpa [F] using h135G
  · intro k hk hn
    have h93k : k ≠ 93 := by intro he; subst k; norm_num at hk
    have h110k : k ≠ 110 := by intro he; subst k; norm_num at hk
    simpa [F,h93k,h110k] using hframe k hk hn

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
