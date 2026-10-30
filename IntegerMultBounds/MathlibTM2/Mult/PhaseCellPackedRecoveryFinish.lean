module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryRhsState
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryInterior
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryRecoveryRhs

/-! Compose an executed recovery RHS with the placed second interior solve.
Its initializer is derived from the original retained state and exact RHS frame. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 248 Q A U}

noncomputable def packedRecoveryFinish (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 248 Q A U :=
  .seq (packedBoundaryRecoveryRhs hQ) (packedRecoveryInterior hR hQ)

theorem packedRecoveryFinish_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l s t p u target rhsExp a b V q w : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (hq : q = executionPrecision p l target rhsExp) (hw : w = executionWidth p l target rhsExp)
    (Y R C : ZMod s → GaussianInt) (hnorm : ∀ i, ‖value q (R i)‖ ≤ (2 : ℝ)^rhsExp)
    (hab : a ≤ b) (hb : b ≤ s) (hband : PhaseCellBand.width p u ≤ s)
    (hwide : 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^V)
    (hVeq : V = weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (2*executionPrecision p l target rhsExp+8) t u)
    (hwV : executionWidth p l target rhsExp < 2^V)
    (hcoords : b < 2^V) (hunits : b*executionWidth p l target rhsExp < 2^V)
    (solutionTail outputTail rhsTail : List (Fin (A+4)))
    (v v₁ : HS 248 Q A U) (S : Stacks 248 A) (n₁ : ℕ)
    (huser : v₁.user = v.user)
    (he₁ : Exec body (packedBoundaryRecoveryRhs hQ) (mk v S) n₁
      (mk v₁ (packedRecoveryRhsState w a b Y R C solutionTail outputTail rhsTail S)))
    (hwork : PackedBoundarySolveWorkspace q (embStk packedBoundaryRecoveryBase S))
    (hheaders : CouplingMasterHeaders (2^15*p) q w s t u (PhaseCellBand.width p u) a b
      (embStk packedRecoveryRuntimeReg S))
    (hstage : (S.R 118).length = executionStagePrecision p l target rhsExp+1)
    (hlevel : (S.R 120).length = l)
    (hnative : ∀ i : Fin 117, i ≠ 93 → i ≠ 110 → i ≠ 116 → S.R ⟨i.val,by omega⟩ = [])
    (hmeta : CouplingIntervalMetadata V s t (PhaseCellBand.width p u) a b a (b-a)
      (embStk packedRecoveryRuntimeReg S))
    (hclean : ∀ k ∈ ([127,129,131,133,134,135,136,153,158,166] : List (Fin 248)), S.R k = [])
    (hfresh : ∀ k : Fin 248, 242 ≤ k.val → S.R k = [])
    (hrange : EncodedRange A w q (interiorOutputExponent p l target rhsExp)
      (cstream A w (packedInterval a (b-a) Y)))
    (xI : ZMod s → ℝ)
    (hxI : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b)
      xI (fun i => (value q (R i)).re)) :
    ∃ v' F n E', ∃ D : ZMod s → GaussianInt, v'.user = v.user ∧
      n ≤ n₁+(initializeHaloLengthKeysCost (2^15*p) (executionStagePrecision p l target rhsExp+1)
        (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) a b+
        packedHaloKeyLoopCost p l s t u target rhsExp a b V (haloLengthKeys s t (PhaseCellBand.width p u) a b)+1) ∧
      Exec body (packedRecoveryFinish hR hQ) (mk v S) n (mk v' F) ∧
      F.R 93 = S.R 93 ∧ F.R 139 = S.R 139 ∧ F.R 238 = solutionTail ∧ F.inp = S.inp ∧ F.out = S.out ∧
      PackedHaloReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
        q l s t u (PhaseCellBand.width p u) a b V w
        (cstream A w (packedInterval a (b-a) R)++(cstream A w (packedInterval a (b-a) C)++rhsTail))
        E' outputTail (embStk packedRecoveryInteriorReg F) ∧
      F.R 132 = cstream A w (packedInterval a (b-a) D)++outputTail ∧
      (∀ i, ‖value q (D i)‖ ≤ (2 : ℝ)^interiorOutputExponent p l target rhsExp) ∧
      (∀ i, Fits w (D i)) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t (PhaseCellBand.width p u) a b)
        (fun i => (value q (D i)).re) xI (1/(2 : ℝ)^target) ∧
      PackedHaloWordFrame s t (PhaseCellBand.width p u) a b w
        (cstream A w (packedInterval a (b-a) Y)++outputTail) (F.R 132) ∧ F.L = S.L ∧
      (∀ k ∈ packedRecoveryRetainedPorts, F.R k = S.R k) ∧
      F.R 245 = [] ∧ F.R 246 = [] ∧
      (F.R 243).length ≤ ((s/(t-s)+1)-2*PhaseCellBand.width p u) ∧
      (∀ k : Fin 248, 168 ≤ k.val → k.val < 242 → k ≠ 238 → F.R k = S.R k) ∧
      F.R 127 = [] ∧ F.R 143 = S.R 143 ∧ F.R 158 = S.R 158 ∧ F.R 167 = [] ∧ F.R 126 = S.R 126 := by
  let H := packedRecoveryRhsState w a b Y R C solutionTail outputTail rhsTail S
  have hinit := packedRecoveryInteriorReady_after_rhs hab hb Y R C solutionTail outputTail rhsTail S
    hwork hheaders hstage hlevel hnative hmeta hclean hfresh
  have hread93 : (embStk packedRecoveryInteriorReg H).R 93 = H.R 93 :=
    congrArg H.R (packedRecoveryInteriorReg_fixed 93 (by decide))
  obtain ⟨v₂,F,n₂,E',D,hu₂,hn₂,he₂,h93,h139,hi,ho,hready,houtput,hDnorm,hDfits,herror,hwords,hleft,
    hoff,hretained,h245,h246,hlength,hfactors,h127,hsmall,hqueue⟩ := packedRecoveryInterior_field_exec (body := body) hR hQ hA hp hst hu
    hαu hθ hgap hbudget hpad R (by simpa only [← hq] using hnorm) hab hb hband hwide hVeq
    hwV hcoords hunits (cstream A w (packedInterval a (b-a) C)++rhsTail)
    (cstream A w (packedInterval a (b-a) Y)) outputTail v₁ H
    (by rw [hread93]; simpa only [← hw] using hinit.native) (by simpa only [← hq] using hinit.masters)
    hinit.lower hinit.upper hinit.metadata hinit.binaryLengthBound hinit.output
    (by simpa only [← hw] using hinit.length) hinit.fresh
    (by simpa only [← hq,← hw] using hrange) xI (by simpa only [← hq] using hxI)
  refine ⟨v₂,F,n₁+n₂,E',D,hu₂.trans huser,by omega,Exec.seq he₁ he₂,h93,h139,?_,hi,ho,?_,?_,?_,?_,?_,?_,hleft,?_,h245,h246,hlength,?_,h127,?_,?_,?_,?_⟩
  · simpa [H,packedRecoveryRhsState] using (hfactors 238 (by decide) (by decide)).2
  · simpa only [← hq,← hw] using hready
  · simpa only [← hw] using houtput
  · simpa only [← hq] using hDnorm
  · simpa only [← hw] using hDfits
  · simpa only [← hq] using herror
  · simpa [← hw,H,packedRecoveryRhsState] using hwords
  · intro k hk
    have hh := (hretained k hk).2
    have hs := packedRecoveryRetainedPorts_safe k hk
    have h238 : k ≠ 238 := by intro he; have hh := hs.2.1; subst k; norm_num at hh
    have h110 : k ≠ 110 := by intro he; have hh := hs.1; subst k; norm_num at hh
    have h116 : k ≠ 116 := by intro he; have hh := hs.1; subst k; norm_num at hh
    simpa only [H,packedRecoveryRhsState,Function.update_of_ne h238,
      Function.update_of_ne hs.2.2.1,Function.update_of_ne h110,
      Function.update_of_ne h116,Function.update_of_ne hs.2.2.2.1] using hh
  · intro k hk hk' h238
    have hh := (hfactors k hk hk').2
    have hv238 : k.val ≠ 238 := fun he => h238 (Fin.ext he)
    simpa [H,packedRecoveryRhsState,Function.update_apply,Fin.ext_iff,hv238,
      show k.val ≠ 132 by omega,show k.val ≠ 110 by omega,
      show k.val ≠ 116 by omega,show k.val ≠ 167 by omega] using hh
  · simpa [H,packedRecoveryRhsState] using hsmall 143 (by decide)
  · simpa [H,packedRecoveryRhsState] using hsmall 158 (by decide)
  · simpa [H,packedRecoveryRhsState] using hsmall 167 (by decide)

  · simpa [H,packedRecoveryRhsState] using hqueue

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
