module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRunHaloKeys
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateHaloLengthKeys
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloKeysCore

/-! The runtime-selected positive distinct schedule executes the complete
interior, retaining the uniform core error on the final physical ambient line. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem runGeneratedHaloKeys_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l s t p u target rhsExp V a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hwide : s < 2^V)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re))
    (v : HS 144 Q A U) (S : Stacks 144 A) (borrowed E outputTail keyTail : List (Fin (A+4)))
    (hE : E.length = s*executionWidth p l target rhsExp) (hdst : S.R 132 = E++outputTail)
    (hkeys : S.R 126 = haloPositiveLengthPackets A V s t (PhaseCellBand.width p u) a b++keyTail)
    (hcount : S.R 127 = List.replicate (haloLengthKeys s t (PhaseCellBand.width p u) a b).length tick)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) V
      (executionWidth p l target rhsExp) (cstream A (executionWidth p l target rhsExp) (chirpLine s C)++borrowed) S)
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b) :
    let band := PhaseCellBand.width p u
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    ∃ v' S' n, ∃ E' : List (Fin (A+4)), v'.user = v.user ∧
      n ≤ haloLengthKeyLoopCost p l s t u target rhsExp V a b (haloLengthKeys s t band a b)+1 ∧
      Exec (embTab groupReg body) (runHaloKeys hR hQ) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ E'.length = s*w ∧
      S'.R = keyLoopR S.R keyTail [] (E'++outputTail) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t band a b)
        (publishedCellRead q w (0 : ZMod s) (S'.R 132)) x (1/(2 : ℝ)^target) ∧
      (EncodedRange A w q (interiorOutputExponent p l target rhsExp) E →
        EncodedRange A w q (interiorOutputExponent p l target rhsExp) E') := by
  dsimp only
  let band := PhaseCellBand.width p u
  have hbounds : ∀ L ∈ haloLengthKeys s t band a b,
      0 < L ∧ L ≤ s ∧ L+L ≤ 2^l+1 ∧ L < 2^V := by
    intro L hL
    have hpos : 0 < L := of_decide_eq_true (List.mem_filter.mp hL).2
    have hc : L ∈ haloLengthCandidates s t band a b :=
      List.mem_dedup.mp (List.mem_filter.mp hL).1
    have huniform := haloLengthCandidates_uniform hst band a b hc
    have hdiv := Nat.div_le_self s (t-s)
    have hb := PhaseCellBand.width_pos p u
    have hLs : L ≤ s := by dsimp only [band] at *; omega
    exact ⟨hpos,hLs,haloLengthKeys_pad hst band a b l hpad L hL,hLs.trans_lt hwide⟩
  obtain ⟨v',S',n,E',hu',hn,he,hi,ho,hl,hlen,hframe,herror,hkeep,hbound⟩ := runHaloKeys_spec (body := body)
    hR hQ hA hp hst hu hαu hθ hgap hbudget hband has hbs (haloLengthKeys s t band a b)
    (haloLengthKeys_nodup s t band a b) hbounds C hC x hx v S borrowed E outputTail keyTail hE hdst
    (by simpa only [lengthKeyPackets,haloPositiveLengthPackets] using hkeys) hcount hready haMaster hbMaster
  refine ⟨v',S',n,E',hu',hn,he,hi,ho,hl,hlen,hframe,?_,hbound⟩
  exact haloLengthKeys_errorOn hst band a b _ x _ herror

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
