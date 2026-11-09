module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloLengthKeyLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloLengthKeyLoopSharedStock

/-! All runtime-selected classes share one maximum workspace reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def haloLengthKeyLoopWorkspace (J R K p l s t u target rhsExp V a b : ℕ) (keys : List ℕ) : ℕ :=
  haloLengthKeyLoopSharedWorkspace J R K p l s t u target rhsExp V a b keys

theorem haloLengthKeyLoop_spec_within (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l s t p u target rhsExp V a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (keys : List ℕ) (hnodup : keys.Nodup)
    (hbounds : ∀ L ∈ keys, 0 < L ∧ L ≤ s ∧ L+L ≤ 2^l+1 ∧ L < 2^V)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re))
    (J R K : ℕ)
    (hpushJ : mnProgPush (rmulOne (P := P₀) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ J)
    (hpushR : mnProgPush (rpProg (P := P₀) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ R)
    (hpushK : mnProgPush (cmulBlock cr
      (rmulOne (P := P₀) (Q := Q) (A := A) (U := U) mul mul_injective (by decide) hQ cr)) ≤ K)
    (v : HS 144 Q A U) (S : Stacks 144 A) (borrowed E outputTail keyTail : List (Fin (A+4)))
    (hE : E.length = s*executionWidth p l target rhsExp) (hdst : S.R 132 = E++outputTail)
    (hkeys : S.R 126 = lengthKeyPackets A V keys++keyTail)
    (hcount : S.R 127 = List.replicate keys.length tick)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) V
      (executionWidth p l target rhsExp) (cstream A (executionWidth p l target rhsExp) (chirpLine s C)++borrowed) S)
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hflag : v.flag = keys.head?.isSome) :
    let band := PhaseCellBand.width p u
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    ∃ v' S' n, ∃ E' : List (Fin (A+4)), v'.user = v.user ∧
      n ≤ haloLengthKeyLoopCost p l s t u target rhsExp V a b keys ∧
      ExecWithin (embTab groupReg body)
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
          haloLengthKeyLoopWorkspace J R K p l s t u target rhsExp V a b keys)
        0 (.loop (·.flag) (haloLengthKeyStep hR hQ)) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ E'.length = s*w ∧
      S'.R = keyLoopR S.R keyTail [] (E'++outputTail) ∧
      (∀ L ∈ keys, ∀ n : Fin (haloLengthGroup s t band a b L).length,
        PhaseCellInterface.ErrorOn (publishedCellCore (haloGroupOrigin s t band a b L n) L)
          (publishedCellRead q w (0 : ZMod s) (S'.R 132)) x (1/(2 : ℝ)^target)) ∧
      (∀ K, K ∉ keys → ∀ n : Fin (haloLengthGroup s t band a b K).length, ∀ j ∈ publishedCellCore
        (haloGroupOrigin s t band a b K n) K,
        publishedCellRead q w (0 : ZMod s) (S'.R 132) j = publishedCellRead q w (0 : ZMod s) (S.R 132) j) ∧
      (EncodedRange A w q (interiorOutputExponent p l target rhsExp) E →
        EncodedRange A w q (interiorOutputExponent p l target rhsExp) E') := by
  exact haloLengthKeyLoop_spec_shared_workspace (body := body) hR hQ hA hp hst hu hαu hθ hgap
    hbudget hband has hbs keys hnodup hbounds C hC x hx J R K hpushJ hpushR hpushK
    v S borrowed E outputTail keyTail hE hdst hkeys hcount hready haMaster hbMaster hflag

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
