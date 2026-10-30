module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryRetainedPorts
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryInteriorPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSolvePackedHaloInteriorField

/-! Execute the existing packed interior solver in fresh runtime roles beside
retained boundary factors and the coefficient page. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast ScalarPlacement
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 248 Q A U}

noncomputable def packedRecoveryInterior (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 248 Q A U :=
  embProg packedRecoveryInteriorReg Empty.elim (solvePackedHaloInterior (P := Empty) hR hQ)

theorem packedRecoveryInterior_field_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l s t p u target rhsExp a b V : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (hab : a ≤ b) (hb : b ≤ s) (hband : PhaseCellBand.width p u ≤ s)
    (hwide : 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^V)
    (hVeq : V = weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (2*executionPrecision p l target rhsExp+8) t u)
    (hwV : executionWidth p l target rhsExp < 2^V)
    (hcoords : b < 2^V) (hunits : b*executionWidth p l target rhsExp < 2^V)
    (tail E outputTail : List (Fin (A+4)))
    (v : HS 248 Q A U) (S : Stacks 248 A)
    (hnative : embStk packedCellCoreReg (embStk packedRecoveryInteriorReg S) = releasedCellBank []
      (cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) C)++tail) ((embStk packedRecoveryInteriorReg S).R 93) S.inp S.out)
    (hmasters : ∀ r ∈ groupHeaderCopies, ((embStk packedRecoveryInteriorReg S).R (packedHeaderReg r.1)).length =
      groupHeaderValue (2^15*p) (executionStagePrecision p l target rhsExp+1)
        (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) 0 r.1)
    (ha : ((embStk packedRecoveryInteriorReg S).R 141).length = a) (hb' : ((embStk packedRecoveryInteriorReg S).R 142).length = b)
    (hmeta : CouplingIntervalMetadata V s t (PhaseCellBand.width p u) a b a (b-a) (embStk packedRecoveryInteriorReg S))
    (h157 : ((embStk packedRecoveryInteriorReg S).R 157).length ≤ V)
    (houtput : (embStk packedRecoveryInteriorReg S).R 132 = E++outputTail) (hE : E.length = (b-a)*executionWidth p l target rhsExp)
    (hfresh : ∀ k ∈ [(125 : Fin 168),127,130,133,138,129,131,134,135,136,140,153,166], (embStk packedRecoveryInteriorReg S).R k = [])
    (hrange : EncodedRange A (executionWidth p l target rhsExp) (executionPrecision p l target rhsExp)
      (interiorOutputExponent p l target rhsExp) E)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re)) :
    ∃ v' F n E', ∃ D : ZMod s → GaussianInt, v'.user = v.user ∧
      n ≤ initializeHaloLengthKeysCost (2^15*p) (executionStagePrecision p l target rhsExp+1)
        (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) a b+
        packedHaloKeyLoopCost p l s t u target rhsExp a b V (haloLengthKeys s t (PhaseCellBand.width p u) a b)+1 ∧
      Exec body (packedRecoveryInterior hR hQ) (mk v S) n (mk v' F) ∧
      F.R 93 = S.R 93 ∧ F.R 139 = S.R 139 ∧ F.inp = S.inp ∧ F.out = S.out ∧
      PackedHaloReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
        (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) a b V
        (executionWidth p l target rhsExp)
        (cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) C)++tail)
        E' outputTail (embStk packedRecoveryInteriorReg F) ∧
      F.R 132 = cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) D)++outputTail ∧
      (∀ k, ‖value (executionPrecision p l target rhsExp) (D k)‖ ≤ (2 : ℝ)^interiorOutputExponent p l target rhsExp) ∧
      (∀ k, Fits (executionWidth p l target rhsExp) (D k)) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t (PhaseCellBand.width p u) a b)
        (fun k => (value (executionPrecision p l target rhsExp) (D k)).re) x (1/(2 : ℝ)^target) ∧
      PackedHaloWordFrame s t (PhaseCellBand.width p u) a b (executionWidth p l target rhsExp)
        (S.R 132) (F.R 132) ∧ F.L = S.L ∧
      (∀ k : Fin 248, (∀ i, packedRecoveryInteriorReg i ≠ k) → F.L k = S.L k ∧ F.R k = S.R k) ∧
      (∀ k ∈ packedRecoveryRetainedPorts, F.L k = S.L k ∧ F.R k = S.R k) ∧
      ∀ k : Fin 248, 168 ≤ k.val → k.val < 242 → F.L k = S.L k ∧ F.R k = S.R k := by
  let T := embStk packedRecoveryInteriorReg S
  obtain ⟨v₁,H,n,E',D,hu₁,hn,he,h93,hi,ho,hready,houtput',hDnorm,hDfits,hqueue,hzero,hframe,herror,hwords,hleft⟩ :=
    solvePackedHaloInterior_field_exec (body := fun p : Empty => nomatch p) hR hQ hA hp hst hu hαu hθ hgap hbudget
      hpad C hC hab hb hband hwide hVeq hwV hcoords hunits tail E outputTail
      (embDn packedRecoveryInteriorReg v) T hnative hmasters ha hb' hmeta h157 houtput hE hfresh hrange x hx
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    packedRecoveryInteriorReg_injective (fun p => nomatch p) he v rfl S rfl
  let F := embOvr packedRecoveryInteriorReg H.get S
  have hproj : embStk packedRecoveryInteriorReg F = H :=
    embStk_ovr packedRecoveryInteriorReg_injective H S
  refine ⟨v₂,F,n,E',D,hu₂.trans hu₁,hn,he₂,?_,?_,hi,ho,?_,?_,hDnorm,hDfits,herror,?_,
    embOvr_left_of_eq S H hleft,?_,?_,?_⟩
  · exact (congrArg (fun B : Stacks 168 A => B.R 93) hproj).trans h93
  · exact (congrArg (fun B : Stacks 168 A => B.R 139) hproj).trans
      (hframe 139 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).2
  · rw [hproj]; exact hready
  · exact (congrArg (fun B : Stacks 168 A => B.R 132) hproj).trans houtput'
  · change PackedHaloWordFrame s t (PhaseCellBand.width p u) a b (executionWidth p l target rhsExp)
      (T.R 132) ((embStk packedRecoveryInteriorReg F).R 132)
    rw [hproj]
    exact hwords
  · intro k hk
    exact embOvr_off H.get S hk
  · intro k hk
    exact packedRecoveryRetained_frame F S H hproj
      (fun j hj => embOvr_off H.get S hj) hframe k hk
  · intro k hk hk'
    exact embOvr_off H.get S (fun i => packedRecoveryInteriorReg_avoids_factors i k hk hk')

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
