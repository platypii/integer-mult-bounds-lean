module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreservePackedRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleasePackedHaloKeys

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSolvePackedHaloInteriorField
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedCouplingCoefficientInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializePackedHaloKeys
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloGroupAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellKeyedPackedHaloInput

/-! Preserve the local RHS, execute the full packed interior, and generate its
retained coupling page without changing the field representation or accuracy. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

noncomputable def packedHaloInteriorCoefficients (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 168 Q A U :=
  .seq (preservePackedRhsFrom 119) (.seq (solvePackedHaloInterior hR hQ) (.seq sharedCouplingCoefficientInterval releasePackedHaloKeys))

def packedHaloInteriorPagePorts : List (Fin 168) := [125,126,127,128,130,132,135,138,139,140,143,157]

def packedHaloInteriorCoefficientsCost (p l s t u target rhsExp a b V : ℕ) : ℕ :=
  (16*(b-a)*executionWidth p l target rhsExp+17*(b-a)+11*V+
        8*executionPrecision p l target rhsExp+2*executionWidth p l target rhsExp+36)+
        (initializeHaloLengthKeysCost (2^15*p) (executionStagePrecision p l target rhsExp+1)
        (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) a b+
        packedHaloKeyLoopCost p l s t u target rhsExp a b V (haloLengthKeys s t (PhaseCellBand.width p u) a b)+1+
        sharedCouplingCoefficientIntervalCost (2^15*p) (executionPrecision p l target rhsExp)
          (executionWidth p l target rhsExp) s t u (PhaseCellBand.width p u) a b V)+
        (2*(V+((s/(t-s)+1)-2*PhaseCellBand.width p u))+5)

theorem packedHaloInteriorCoefficients_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (hrange : EncodedRange A (executionWidth p l target rhsExp) (executionPrecision p l target rhsExp)
      (interiorOutputExponent p l target rhsExp) E)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re)) :
    ∃ v' G m, ∃ D : ZMod s → GaussianInt, v'.user = v.user ∧
      m ≤ packedHaloInteriorCoefficientsCost p l s t u target rhsExp a b V ∧
      Exec body (packedHaloInteriorCoefficients hR hQ) (mk v S) m (mk v' G) ∧
      G.R 93 = cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) C)++S.R 93 ∧ G.inp = S.inp ∧ G.out = S.out ∧
      G.R 132 = cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) D)++outputTail ∧
      (∀ k, ‖value (executionPrecision p l target rhsExp) (D k)‖ ≤ (2 : ℝ)^interiorOutputExponent p l target rhsExp) ∧
      (∀ k, Fits (executionWidth p l target rhsExp) (D k)) ∧
      embStk packedCellCoreReg G = releasedCellBank []
        (cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) C)++tail) (G.R 93) G.inp G.out ∧
      CouplingReady (2^15*p) (executionPrecision p l target rhsExp) (executionWidth p l target rhsExp)
        s t u (PhaseCellBand.width p u) a b
        (cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) C)++tail)
        (embStk sharedCouplingCoreReg G) ∧
      CouplingIntervalMetadata V s t (PhaseCellBand.width p u) a b a (b-a) G ∧
      G.R 138 = cstream A (executionWidth p l target rhsExp)
        (couplingCoefficientPageInterval (2^15*p) (executionPrecision p l target rhsExp)
          s t u (PhaseCellBand.width p u) a b a (b-a)) ∧
      G.R 139 = List.replicate (couplingCoefficientPageInterval (2^15*p) (executionPrecision p l target rhsExp)
        s t u (PhaseCellBand.width p u) a b a (b-a)).length tick ∧
      G.R 140 = List.replicate (2*PhaseCellBand.width p u+1) tick ∧ G.R 143 = [] ∧ G.R 135 = [] ∧
      G.R 126 = S.R 126 ∧ G.R 127 = [] ∧
      (∀ k : Fin 168, 117 ≤ k.val → k ∉ packedHaloInteriorPagePorts → G.L k = S.L k ∧ G.R k = S.R k) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t (PhaseCellBand.width p u) a b)
        (fun k => (value (executionPrecision p l target rhsExp) (D k)).re) x (1/(2 : ℝ)^target) ∧ G.L = S.L ∧ G.R 125 = [] ∧ G.R 128 = [] := by
  let rhs := cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) C)
  have hfit : a+(b-a) ≤ s := by omega
  have hqmaster : (S.R 119).length = executionPrecision p l target rhsExp := by
    simpa [packedHeaderReg,groupHeaderValue] using hmasters (119,112) (by decide)
  have hsource : S.R 110 = rhs++tail := by
    simpa [embStk,packedCellCoreReg,releasedCellBank,rhs] using
      congrArg (fun B : Stacks 117 A => B.R 110) hnative
  have hclean : ∀ k ∈ [(0 : Fin 168),1,2,94,104,105,108,166], S.R k = [] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
    | simpa [embStk,packedCellCoreReg,releasedCellBank] using congrArg (fun B : Stacks 117 A => B.R 0) hnative
    | simpa [embStk,packedCellCoreReg,releasedCellBank] using congrArg (fun B : Stacks 117 A => B.R 1) hnative
    | simpa [embStk,packedCellCoreReg,releasedCellBank] using congrArg (fun B : Stacks 117 A => B.R 2) hnative
    | simpa [embStk,packedCellCoreReg,releasedCellBank] using congrArg (fun B : Stacks 117 A => B.R 94) hnative
    | simpa [embStk,packedCellCoreReg,releasedCellBank] using congrArg (fun B : Stacks 117 A => B.R 104) hnative
    | simpa [embStk,packedCellCoreReg,releasedCellBank] using congrArg (fun B : Stacks 117 A => B.R 105) hnative
    | simpa [embStk,packedCellCoreReg,releasedCellBank] using congrArg (fun B : Stacks 117 A => B.R 108) hnative
    | exact hfresh 166 (by simp)
  obtain ⟨v₀,m₀,hu₀,hm₀,he₀⟩ := preservePackedRhsFrom_exec (body := body) 119 (by decide)
    V (b-a) (executionPrecision p l target rhsExp) (executionWidth p l target rhsExp)
    (by omega) (by dsimp [executionWidth,executionPrecision]; omega) rhs tail
    (by simp [rhs,packedInterval_length C hfit]) v S hqmaster hmeta.count hsource hclean
  let B : Stacks 168 A := {S with R := Function.update S.R 93 (rhs++S.R 93)}
  have hnativeB : embStk packedCellCoreReg B = releasedCellBank []
      (cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) C)++tail) (B.R 93) B.inp B.out := by
    have hv := embStk_updateR packedCellCoreReg_injective S 93 (rhs++S.R 93)
    change embStk packedCellCoreReg B = _ at hv
    rw [hv,hnative]
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k = 93
    · subst k; simp [B,releasedCellBank]
    · have hval : k.val ≠ 93 := fun he => hk (Fin.ext he)
      simp [B,releasedCellBank,hk,hval]
  have hmastersB : ∀ r ∈ groupHeaderCopies, (B.R (packedHeaderReg r.1)).length =
      groupHeaderValue (2^15*p) (executionStagePrecision p l target rhsExp+1)
        (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) 0 r.1 := by
    intro r hr
    have hn : packedHeaderReg r.1 ≠ 93 := by
      simp only [groupHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [B,hn] using hmasters r hr
  have hmetadataB : CouplingIntervalMetadata V s t (PhaseCellBand.width p u) a b a (b-a) B := by
    constructor
    · simpa [B] using hmeta.width
    · intro k hk
      have hn : k ≠ 93 := by
        simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simpa [B,hn] using hmeta.encoded k hk
  obtain ⟨v₁,F,m₁,E',D,hu₁,hm₁,he₁,h93,hi,ho,hrdy,hout,hDnorm,hDfits,hqueue,hzero,hframeB,herror,hwords,hleftAll,hlength⟩ :=
    solvePackedHaloInterior_field_exec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget hpad C hC
      hab hb hband (by omega) hVeq hwV hcoords hunits tail E outputTail v₀ B hnativeB hmastersB
      (by simpa [B] using ha) (by simpa [B] using hb') hmetadataB (by simpa [B] using h157)
      (by simpa [B] using houtput) hE
      (by
        intro k hk
        have hn : k ≠ 93 := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        simpa [B,hn] using hfresh k hk) hrange x hx
  have hframe : ∀ k : Fin 168, 117 ≤ k.val → k ≠ 125 → k ≠ 130 → k ≠ 126 → k ≠ 127 →
      k ≠ 128 → k ≠ 157 → k ≠ 132 → F.L k = S.L k ∧ F.R k = S.R k := by
    intro k hk h125 h130 h126 h127 h128 h157 h132
    have hn : k ≠ 93 := by intro he; subst k; norm_num at hk
    simpa [B,hn] using hframeB k hk h125 h130 h126 h127 h128 h157 h132
  have hqueue' : F.R 126 = S.R 126 := by simpa [B] using hqueue
  have hpass (k : Fin 168) (hk : 117 ≤ k.val) (h125 : k ≠ 125) (h130 : k ≠ 130)
      (h126 : k ≠ 126) (h127 : k ≠ 127) (h128 : k ≠ 128) (h157 : k ≠ 157) (h132 : k ≠ 132) :=
    (hframe k hk h125 h130 h126 h127 h128 h157 h132).2
  have haF : (F.R 141).length = a := by
    rw [hpass 141 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact ha
  have hbF : (F.R 142).length = b := by
    rw [hpass 142 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hb'
  have hleftF : ∀ k ∈ [(121 : Fin 168),122,123,124], F.L k = [] := by
    intro k hk
    have hn : 117 ≤ k.val ∧ k ≠ 125 ∧ k ≠ 130 ∧ k ≠ 126 ∧ k ≠ 127 ∧ k ≠ 128 ∧ k ≠ 157 ∧ k ≠ 132 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> decide
    rw [(hframe k hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2.1 hn.2.2.2.2.2.2.1 hn.2.2.2.2.2.2.2).1]
    exact hleft k hk
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := PackedHaloReady.coefficient_exec (body := body)
    (by omega) (by omega) hst hab hb haLt hwide hfitV _ E' outputTail v₁ F hrdy haF hbF hleftF
    (by rw [hpass 139 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h139)
    (by rw [hpass 143 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h143)
  let xs := couplingCoefficientPageInterval (2^15*p) (executionPrecision p l target rhsExp)
    s t u (PhaseCellBand.width p u) a b a (b-a)
  let H := sharedCouplingPageState (PhaseCellBand.width p u) (executionWidth p l target rhsExp) xs F
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := releasePackedHaloKeys_exec (body := body) V ((s/(t-s)+1)-2*PhaseCellBand.width p u) v₂ H
    (by simpa [H,sharedCouplingPageState] using hrdy.keyWidth)
    (by simpa [H,sharedCouplingPageState] using hlength)
  let G := releasedPackedHaloKeys H
  have hcoupling : CouplingReady (2^15*p) (executionPrecision p l target rhsExp) (executionWidth p l target rhsExp)
      s t u (PhaseCellBand.width p u) a b
      (cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) C)++tail)
      (embStk sharedCouplingCoreReg G) := by
    rw [show embStk sharedCouplingCoreReg G = embStk sharedCouplingCoreReg H from releasedPackedHaloKeys_core H,
      show embStk sharedCouplingCoreReg H = embStk sharedCouplingCoreReg F from sharedCouplingPage_core _ _ _ _]
    exact hrdy.coupling haF hbF hleftF
  have hmetadata : CouplingIntervalMetadata V s t (PhaseCellBand.width p u) a b a (b-a) G := by
    constructor
    · simpa [G,H,releasedPackedHaloKeys,sharedCouplingPageState] using hrdy.metadata.width
    · intro k hk
      have hn (j : Fin 168) (hj : j.val < 145) : k ≠ j := by
        have hhigh : 145 ≤ k.val := by
          simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        intro he; have hv := congrArg (fun k : Fin 168 => k.val) he; omega
      simpa [G,H,releasedPackedHaloKeys,sharedCouplingPageState,hn 135 (by decide),hn 138 (by decide),hn 139 (by decide),
        hn 140 (by decide),hn 143 (by decide),hn 125 (by decide),hn 128 (by decide)] using hrdy.metadata.encoded k hk
  refine ⟨v₃,G,m₀+(m₁+(m₂+m₃)),D,hu₃.trans (hu₂.trans (hu₁.trans hu₀)),by dsimp only [packedHaloInteriorCoefficientsCost]; omega,Exec.seq he₀ (Exec.seq he₁ (Exec.seq he₂ he₃)),?_,hi,ho,?_,hDnorm,hDfits,
    ?_,hcoupling,hmetadata,?_,?_,?_,?_,?_,?_,?_,?_,herror,hleftAll,by simp [G,releasedPackedHaloKeys]⟩
  · simpa [G,H,releasedPackedHaloKeys,sharedCouplingPageState,B,rhs] using h93
  · simpa [G,H,releasedPackedHaloKeys,sharedCouplingPageState] using hout
  · change embStk packedCellCoreReg (releasedPackedHaloKeys H) = _
    rw [releasedPackedHaloKeys_native,show H = sharedCouplingPageState _ _ _ F from rfl,sharedCouplingPage_native]
    simpa [G,H,releasedPackedHaloKeys,sharedCouplingPageState] using hrdy.native
  · have h138F : F.R 138 = [] := by
      rw [hpass 138 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hfresh 138 (by simp)
    simp [G,H,releasedPackedHaloKeys,sharedCouplingPageState,xs,h138F]
  · simp [G,H,releasedPackedHaloKeys,sharedCouplingPageState,xs]
  · simp [G,H,releasedPackedHaloKeys,sharedCouplingPageState]
  · simp [G,H,releasedPackedHaloKeys,sharedCouplingPageState]
  · simp [G,H,releasedPackedHaloKeys,sharedCouplingPageState]
  · simpa [G,H,releasedPackedHaloKeys,sharedCouplingPageState] using hqueue'
  · simpa [G,H,releasedPackedHaloKeys,sharedCouplingPageState] using hzero
  · intro k hk hnot
    have hn (j : Fin 168) (hj : j ∈ packedHaloInteriorPagePorts) : k ≠ j := by
      intro he; subst k; exact hnot hj
    obtain ⟨hl,hr⟩ := hframe k hk (hn 125 (by decide)) (hn 130 (by decide)) (hn 126 (by decide))
      (hn 127 (by decide)) (hn 128 (by decide)) (hn 157 (by decide)) (hn 132 (by decide))
    exact ⟨hl,by simpa only [G,H,releasedPackedHaloKeys,sharedCouplingPageState,Function.update_of_ne (hn 143 (by decide)),
      Function.update_of_ne (hn 139 (by decide)),Function.update_of_ne (hn 138 (by decide)),
      Function.update_of_ne (hn 135 (by decide)),Function.update_of_ne (hn 140 (by decide)),
      Function.update_of_ne (hn 125 (by decide)),Function.update_of_ne (hn 128 (by decide))] using hr⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
