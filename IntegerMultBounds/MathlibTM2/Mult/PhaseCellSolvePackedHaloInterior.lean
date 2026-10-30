module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRunGeneratedPackedHaloKeys
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializePackedHaloKeys
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloGroupAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellKeyedPackedHaloInput

/-! Initialize and execute the generated packed halo interior schedule from
retained parameters, preserving the source and the caller's queue suffix. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

noncomputable def solvePackedHaloInterior (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 168 Q A U :=
  .seq initializePackedHaloKeys (runPackedHaloKeys hR hQ)

theorem solvePackedHaloInterior_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re)) :
    ∃ v' F m E', v'.user = v.user ∧
      m ≤ initializeHaloLengthKeysCost (2^15*p) (executionStagePrecision p l target rhsExp+1)
        (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) a b+
        packedHaloKeyLoopCost p l s t u target rhsExp a b V (haloLengthKeys s t (PhaseCellBand.width p u) a b)+1 ∧
      Exec body (solvePackedHaloInterior hR hQ) (mk v S) m (mk v' F) ∧
      F.R 93 = S.R 93 ∧ F.inp = S.inp ∧ F.out = S.out ∧
      PackedHaloReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
        (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) a b V
        (executionWidth p l target rhsExp)
        (cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) C)++tail) E' outputTail F ∧
      F.R 126 = S.R 126 ∧ F.R 127 = [] ∧
      (∀ k : Fin 168, 117 ≤ k.val → k ≠ 125 → k ≠ 130 → k ≠ 126 → k ≠ 127 → k ≠ 128 → k ≠ 157 → k ≠ 132 →
        F.L k = S.L k ∧ F.R k = S.R k) ∧
      (∀ M ∈ haloLengthKeys s t (PhaseCellBand.width p u) a b, PackedCellOutputSpec t p u l target rhsExp M
        (haloPackedOffsets s t (PhaseCellBand.width p u) a b M)
        (packedCellOrigin (s := s) a (haloPackedOffsets s t (PhaseCellBand.width p u) a b M))
        (fun _ => C) (F.R 132)) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t (PhaseCellBand.width p u) a b)
        (fun j => (packedIntervalRead (executionPrecision p l target rhsExp)
          (executionWidth p l target rhsExp) a (F.R 132) j).re) x (1/(2 : ℝ)^target) ∧
      (EncodedRange A (executionWidth p l target rhsExp) (executionPrecision p l target rhsExp)
        (interiorOutputExponent p l target rhsExp) E →
        EncodedRange A (executionWidth p l target rhsExp) (executionPrecision p l target rhsExp)
          (interiorOutputExponent p l target rhsExp) E') ∧
      PackedHaloWordFrame s t (PhaseCellBand.width p u) a b (executionWidth p l target rhsExp)
        (S.R 132) (F.R 132) ∧ F.L = S.L ∧
      (F.R 128).length ≤ ((s/(t-s)+1)-2*PhaseCellBand.width p u) := by
  have hw : executionWidth p l target rhsExp = 2*executionPrecision p l target rhsExp+8 := by
    simp only [executionWidth,executionPrecision]
    omega
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁,hready₁⟩ := initializePackedHaloKeys_exec (body := body)
    (2^15*p) (executionStagePrecision p l target rhsExp+1) (executionPrecision p l target rhsExp)
    l s t u (PhaseCellBand.width p u) a b (by omega) (NeZero.pos s) hst hu hband hab hb (by omega)
    v S _ E outputTail hnative hmasters ha hb'
    (by simpa only [hVeq] using hmeta) (by simpa only [hVeq] using h157)
    houtput (by simpa only [← hw] using hE) hfresh
  rw [← hVeq] at he₁ hready₁
  rw [← hw] at he₁ hready₁
  let B : Stacks 168 A := {S with R := (initializedKeyRuntimeR S.R V (executionWidth p l target rhsExp)
    (haloLengthKeys s t (PhaseCellBand.width p u) a b).length
    (haloPositiveLengthPackets A V s t (PhaseCellBand.width p u) a b))}
  obtain ⟨v₂,F,m₂,E',hu₂,hm₂,he₂,h93,hi,ho,hrdy,hqueue,hzero,hframe,haccuracy,herror,hrange,hwords,hleftAll,hlength⟩ :=
    runGeneratedPackedHaloKeys_exec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget hpad C hC
      hab hb hband hwide hVeq hwV hcoords hunits tail (S.R 126) E outputTail v₁ B hready₁
      (by simp [B,initializedKeyRuntimeR,haloPositiveLengthPackets])
      (by simp [B,initializedKeyRuntimeR]) x hx
  refine ⟨v₂,F,m₁+m₂,E',hu₂.trans hu₁,by omega,Exec.seq he₁ he₂,
    by simpa [B,initializedKeyRuntimeR] using h93,hi,ho,hrdy,hqueue,hzero,?_,haccuracy,herror,hrange,(by simpa [B,initializedKeyRuntimeR] using hwords),hleftAll,?_⟩
  · intro k hk hn125 hn130 hn126 hn127 hn128 hn157 hn132
    obtain ⟨hl,hr⟩ := hframe k hk hn126 hn127 hn128 hn157 hn132
    exact ⟨hl,by simpa only [B,initializedKeyRuntimeR,Function.update_of_ne hn125,
      Function.update_of_ne hn126,Function.update_of_ne hn127,Function.update_of_ne hn130] using hr⟩
  · have h128 : S.R 128 = [] := by
      have hh := hmasters (128,102) (by decide)
      simpa [packedHeaderReg,groupHeaderValue] using hh
    simpa [B,initializedKeyRuntimeR,h128] using hlength

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
