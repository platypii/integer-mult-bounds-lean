module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloSolve

/-! The local solver's existing input contract, shared by concrete callers.
It contains no execution premise or assumed intermediate numerical result. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry ScalarPlacement

/-- Geometry supplied to setup: a fresh bank or a retained interval bank. -/
def PackedHaloGeometryInput {A : ℕ} (freshGeometry : Bool) (V s t band a b : ℕ)
    (S : Stacks 242 A) : Prop :=
  if freshGeometry then
    (∀ k ∈ [(145 : Fin 242),146,147,148,149,151,154,156,164], S.R k = [])
  else CouplingIntervalMetadata V s t band a b a (b-a) (embStk packedHaloRuntimeReg S)

theorem PackedHaloGeometryInput.of_frame {A V s t band a b : ℕ} {freshGeometry : Bool}
    {S F : Stacks 242 A} (h : PackedHaloGeometryInput freshGeometry V s t band a b S)
    (hframe : ∀ k : Fin 242, 145 ≤ k.val → k.val < 168 → F.R k = S.R k) :
    PackedHaloGeometryInput freshGeometry V s t band a b F := by
  cases freshGeometry with
  | true =>
    intro k hk
    have hs : 145 ≤ k.val ∧ k.val < 168 := by
      have hc : ([(145 : Fin 242),146,147,148,149,151,154,156,164]).all
          (fun i => decide (145 ≤ i.val ∧ i.val < 168)) = true := by decide
      simpa only [decide_eq_true_eq] using List.all_eq_true.mp hc k hk
    exact (hframe k hs.1 hs.2).trans (h k hk)
  | false =>
    apply CouplingIntervalMetadata.of_frame h
    · exact hframe 163 (by decide) (by decide)
    · intro k hk
      have hs : 145 ≤ k.val := by
        have hc : couplingIntervalPorts.all (fun i => decide (145 ≤ i.val)) = true := by decide
        simpa only [decide_eq_true_eq] using List.all_eq_true.mp hc k hk
      exact hframe (packedHaloRuntimeReg k) hs k.isLt

structure PackedHaloSetup {A p l s t u target rhsExp a b V : ℕ} [NeZero s]
    (α d : ℝ) (C : ZMod s → GaussianInt)
    (S : Stacks 242 A) (freshGeometry : Bool := true) : Prop where
  hp : 2 ≤ p
  hwidth : 8*p ≤ 2^u
  hα : 0 < α
  hst : s < t
  hu : 1 ≤ u
  hαu : α^2 = (u : ℝ)
  hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1
  hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)
  hbudget : α^2*d ≤ p
  hband : PhaseCellBand.width p u ≤ s
  has : a ≤ s
  hbs : b ≤ s
  hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1
  h109 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 109 = []
  h115 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 115 = []
  h116 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 116 = []
  hleft : ∀ i : Fin 224, (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).L (preparedBoundaryCoreReg i) = []
  hreadyBase : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u
    (boundaryTableBits p (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2+1)
    (executionPrecision p l (initialSchurTarget p u
      (boundaryTableBits p (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)
    l s t u (PhaseCellBand.width p u) 0 0 (S.R 110)
    (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
      (embStk boundaryFactorLegacyReg (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)))))))
  haMaster : ((embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 141).length = a
  hbMaster : ((embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 142).length = b
  h0 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 0 = []
  h139 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 139 = []
  h127 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 127 = []
  h138 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 138 = []
  h143 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 143 = []
  h147 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 147 = []
  h151 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 151 = []
  h153 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 153 = []
  h152 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 152 = []
  hnew : ∀ i : Fin 224, 154 ≤ i.val → (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R (preparedBoundaryCoreReg i) = []
  h132left : S.L 132 = []
  hV : (S.R 163).length = V
  h155 : S.R 155 = binSyms V a
  h165 : S.R 165 = binSyms V (b-a)
  hfitV : a+((b-a)+2*PhaseCellBand.width p u)+s < 2^V
  hgeometry : PackedHaloGeometryInput freshGeometry V s t (PhaseCellBand.width p u) a b S
  h239 : S.R 239 = []
  hab : a ≤ b
  haLt : a < s
  hsep : b-a+PhaseCellBand.width p u ≤ s
  hwide : 8*(t+1)^2+4*PhaseCellBand.width p u+8 < 2^V
  hVeq : V = weightWorkspaceWidth (2^15*p) (executionPrecision p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) (2*(executionPrecision p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp)+8) t u
  hwV : (executionWidth p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) < 2^V
  hcoords : b < 2^V
  hunits : b*(executionWidth p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) < 2^V
  hC : ∀ k, ‖value (executionPrecision p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp
  h157 : (S.R 157).length ≤ V
  h158 : S.R 158 = []
  h167 : S.R 167 = []
  hfresh : ∀ k ∈ [(125 : Fin 168),127,130,133,138,129,131,134,135,136,140,153,166],
    (embStk packedHaloRuntimeReg S).R k = []
  hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ)))

theorem PackedHaloSetup.hgeometryBlank {A p l s t u target rhsExp a b V : ℕ} [NeZero s]
    {α d : ℝ} {C : ZMod s → GaussianInt} {S : Stacks 242 A}
    (h : PackedHaloSetup (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α d C S) :
    ∀ k ∈ [(145 : Fin 242),146,147,148,149,151,154,156,164], S.R k = [] := h.hgeometry

/-- A setup becomes a solver frame once the actual local RHS is attached. -/
structure PackedHaloFrame {A p l s t u target rhsExp a b V : ℕ} [NeZero s]
    (α d : ℝ) (C : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (S : Stacks 242 A) (freshGeometry : Bool := true) : Prop extends
      PackedHaloSetup (p := p) (l := l) (t := t) (u := u) (target := target)
        (rhsExp := rhsExp) (a := a) (b := b) (V := V) α d C S freshGeometry where
  hsource : S.R 110 = cstream A (executionWidth p l
    (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp
      (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp)
    (packedInterval a (b-a) C)++tail

theorem PackedHaloFrame.hready {freshGeometry : Bool} {A p l s t u target rhsExp a b V : ℕ} [NeZero s] {α d : ℝ}
    {C : ZMod s → GaussianInt} {tail : List (Fin (A+4))} {S : Stacks 242 A}
    (h : PackedHaloFrame (freshGeometry := freshGeometry) (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α d C tail S) :
 LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u
    (boundaryTableBits p (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2+1)
    (executionPrecision p l (initialSchurTarget p u
      (boundaryTableBits p (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)
    l s t u (PhaseCellBand.width p u) 0 0 (cstream A (executionWidth p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) (packedInterval a (b-a) C)++tail)
    (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
      (embStk boundaryFactorLegacyReg (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S))))))) := by
  simpa only [h.hsource] using h.hreadyBase

structure PackedHaloInput {A p l s t u target rhsExp a b V : ℕ} [NeZero s]
    (α d : ℝ) (C : ZMod s → GaussianInt) (tail E outputTail : List (Fin (A+4)))
    (S : Stacks 242 A) (freshGeometry : Bool := true) : Prop extends
      PackedHaloFrame (p := p) (l := l) (t := t) (u := u) (target := target)
        (rhsExp := rhsExp) (a := a) (b := b) (V := V) α d C tail S freshGeometry where
  houtput : S.R 132 = E++outputTail
  hE : E.length = (b-a)*(executionWidth p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp)
  hrange : EncodedRange A (executionWidth p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) (executionPrecision p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp)
    (interiorOutputExponent p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) E

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
