module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSolvePackedHaloInterior
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializePackedHaloKeys
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloGroupAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellKeyedPackedHaloInput

/-! The executed packed interior produces a fitting ambient field represented
by its actual local output prefix, with uniform whole-interior accuracy. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

theorem solvePackedHaloInterior_field_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (hrange : EncodedRange A (executionWidth p l target rhsExp) (executionPrecision p l target rhsExp)
      (interiorOutputExponent p l target rhsExp) E)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re)) :
    ∃ v' F m E', ∃ D : ZMod s → GaussianInt, v'.user = v.user ∧
      m ≤ initializeHaloLengthKeysCost (2^15*p) (executionStagePrecision p l target rhsExp+1)
        (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) a b+
        packedHaloKeyLoopCost p l s t u target rhsExp a b V (haloLengthKeys s t (PhaseCellBand.width p u) a b)+1 ∧
      Exec body (solvePackedHaloInterior hR hQ) (mk v S) m (mk v' F) ∧
      F.R 93 = S.R 93 ∧ F.inp = S.inp ∧ F.out = S.out ∧
      PackedHaloReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
        (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) a b V
        (executionWidth p l target rhsExp)
        (cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) C)++tail) E' outputTail F ∧
      F.R 132 = cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) D)++outputTail ∧
      (∀ k, ‖value (executionPrecision p l target rhsExp) (D k)‖ ≤ (2 : ℝ)^interiorOutputExponent p l target rhsExp) ∧
      (∀ k, Fits (executionWidth p l target rhsExp) (D k)) ∧
      F.R 126 = S.R 126 ∧ F.R 127 = [] ∧
      (∀ k : Fin 168, 117 ≤ k.val → k ≠ 125 → k ≠ 130 → k ≠ 126 → k ≠ 127 →
        k ≠ 128 → k ≠ 157 → k ≠ 132 → F.L k = S.L k ∧ F.R k = S.R k) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t (PhaseCellBand.width p u) a b)
        (fun k => (value (executionPrecision p l target rhsExp) (D k)).re) x (1/(2 : ℝ)^target) ∧
      PackedHaloWordFrame s t (PhaseCellBand.width p u) a b (executionWidth p l target rhsExp)
        (S.R 132) (F.R 132) ∧ F.L = S.L ∧
      (F.R 128).length ≤ ((s/(t-s)+1)-2*PhaseCellBand.width p u) := by
  obtain ⟨v',F,m,E',hu',hm,he,h93,hi,ho,hrdy,hqueue,hzero,hframe,haccuracy,herror,hrange',hwords,hleftAll,hlength⟩ :=
    solvePackedHaloInterior_exec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget hpad C hC
      hab hb hband hwide hVeq hwV hcoords hunits tail E outputTail v S hnative hmasters ha hb'
      hmeta h157 houtput hE hfresh x hx
  obtain ⟨D,hE',hDnorm,hDfits⟩ := encodedRange_packedField
    (by dsimp [executionWidth]; omega) (show a+(b-a) ≤ s by omega)
    (interiorOutput_width p l target rhsExp) E' hrdy.length (hrange' hrange)
  have hout : F.R 132 = cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) D)++outputTail :=
    hrdy.output.trans (congrArg (fun xs => xs++outputTail) hE')
  exact ⟨v',F,m,E',D,hu',hm,he,h93,hi,ho,hrdy,hout,hDnorm,hDfits,hqueue,hzero,hframe,
    haloInterior_error_of_packed_outputs hst (by omega) hab hb C D hDfits (F.R 132) outputTail hout haccuracy x hx,hwords,hleftAll,hlength⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
