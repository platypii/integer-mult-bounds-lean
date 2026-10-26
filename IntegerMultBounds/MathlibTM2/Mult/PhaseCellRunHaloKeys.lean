module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloLengthKeyLoop

/-! Enter the counted class loop by inspecting its owned count, and consume
exactly the selected packet prefix while preserving the borrowed suffixes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def runHaloKeys (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  .seq (.act (peekR 127)) (.loop (·.flag) (haloLengthKeyStep hR hQ))

theorem runHaloKeys_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (v : HS 144 Q A U) (S : Stacks 144 A) (borrowed E outputTail keyTail : List (Fin (A+4)))
    (hE : E.length = s*executionWidth p l target rhsExp) (hdst : S.R 132 = E++outputTail)
    (hkeys : S.R 126 = lengthKeyPackets A V keys++keyTail)
    (hcount : S.R 127 = List.replicate keys.length tick)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) V
      (executionWidth p l target rhsExp) (cstream A (executionWidth p l target rhsExp) (chirpLine s C)++borrowed) S)
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b) :
    let band := PhaseCellBand.width p u
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    ∃ v' S' n, ∃ E' : List (Fin (A+4)), v'.user = v.user ∧
      n ≤ haloLengthKeyLoopCost p l s t u target rhsExp V a b keys+1 ∧
      Exec (embTab groupReg body) (runHaloKeys hR hQ) (mk v S) n (mk v' S') ∧
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
  dsimp only
  have hpeek := Exec.act (body := embTab groupReg body) (peekR 127) (mk v S)
  rw [peekR_run,hcount,count_head_isSome keys] at hpeek
  obtain ⟨v',S',n,E',hu',hn,he,hi,ho,hl,hlen,hframe,herror,hkeep,hbound⟩ := haloLengthKeyLoop_spec (body := body)
    hR hQ hA hp hst hu hαu hθ hgap hbudget hband has hbs keys hnodup hbounds C hC x hx
    { v with flag := keys.head?.isSome } S borrowed E outputTail keyTail hE hdst hkeys hcount hready haMaster hbMaster rfl
  exact ⟨v',S',n+1,E',hu',by omega,(Exec.seq hpeek he).cast (by omega) rfl,hi,ho,hl,hlen,hframe,herror,hkeep,hbound⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
