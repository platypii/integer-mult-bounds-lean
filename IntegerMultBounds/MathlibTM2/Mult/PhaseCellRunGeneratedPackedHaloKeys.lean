module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloKeyLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloGroupAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellKeyedPackedHaloInput

/-! Execute the generated halo length schedule and obtain the uniform interior
error bound directly on physical reads of the final local publication buffer. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

noncomputable def runPackedHaloKeys (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 168 Q A U :=
  .seq (.act (peekR 127)) (.loop (·.flag) (packedHaloKeyStep hR hQ))

theorem runGeneratedPackedHaloKeys_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (tail suffix E outputTail : List (Fin (A+4)))
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hready : PackedHaloReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) a b V
      (executionWidth p l target rhsExp)
      (cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) C)++tail) E outputTail S)
    (hkeys : S.R 126 = (haloLengthKeys s t (PhaseCellBand.width p u) a b).flatMap (binSyms V)++suffix)
    (hcount : S.R 127 = List.replicate (haloLengthKeys s t (PhaseCellBand.width p u) a b).length tick)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re)) :
    ∃ v' F m E', v'.user = v.user ∧
      m ≤ packedHaloKeyLoopCost p l s t u target rhsExp a b V (haloLengthKeys s t (PhaseCellBand.width p u) a b)+1 ∧
      Exec body (runPackedHaloKeys hR hQ) (mk v S) m (mk v' F) ∧
      F.R 93 = S.R 93 ∧ F.inp = S.inp ∧ F.out = S.out ∧
      PackedHaloReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
        (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) a b V
        (executionWidth p l target rhsExp)
        (cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) C)++tail) E' outputTail F ∧
      F.R 126 = suffix ∧ F.R 127 = [] ∧
      (∀ k : Fin 168, 117 ≤ k.val → k ≠ 126 → k ≠ 127 → k ≠ 128 → k ≠ 157 → k ≠ 132 →
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
        (S.R 132) (F.R 132) ∧ F.L = S.L := by
  let keys := haloLengthKeys s t (PhaseCellBand.width p u) a b
  have hbounds : ∀ L ∈ keys, 0 < L ∧ L ≤ s ∧ L+L ≤ 2^l+1 ∧ L < 2^V := by
    intro L hL
    have hpos : 0 < L := of_decide_eq_true (List.mem_filter.mp hL).2
    have hc : L ∈ haloLengthCandidates s t (PhaseCellBand.width p u) a b :=
      List.mem_dedup.mp (List.mem_filter.mp hL).1
    have huniform := haloLengthCandidates_uniform hst (PhaseCellBand.width p u) a b hc
    have hdiv := Nat.div_le_self s (t-s)
    have hbandpos := PhaseCellBand.width_pos p u
    have hLs : L ≤ s := by omega
    have hswide : s < 2^V := by nlinarith only [hwide,hst]
    exact ⟨hpos,hLs,haloLengthKeys_pad hst (PhaseCellBand.width p u) a b l hpad L hL,hLs.trans_lt hswide⟩
  let v₀ : HS 168 Q A U := {v with flag := (S.R 127).head?.isSome}
  have hpeek : Exec body (.act (peekR 127)) (mk v S) 1 (mk v₀ S) := by
    simpa only [peekR_run,v₀] using Exec.act (body := body) (peekR 127) (mk v S)
  obtain ⟨v',F,m,E',hu',hm,he,h93,hi,ho,hrdy,hqueue,hzero,hframe,haccuracy,hrange,hwords,hleftAll⟩ := packedHaloKeyLoop_exec (body := body)
    hR hQ hA hp hst hu hαu hθ hgap hbudget keys hbounds C hC hab hb hband hwide hVeq hwV hcoords hunits
    tail suffix E outputTail [] v₀ S hready hkeys hcount
    (by
      change (S.R 127).head?.isSome = keys.head?.isSome
      have hc : S.R 127 = List.replicate keys.length tick := hcount
      rw [hc]
      cases keys <;> simp [List.replicate_succ]) (by simp)
  have hall : ∀ M ∈ keys, PackedCellOutputSpec t p u l target rhsExp M
      (haloPackedOffsets s t (PhaseCellBand.width p u) a b M)
      (packedCellOrigin (s := s) a (haloPackedOffsets s t (PhaseCellBand.width p u) a b M))
      (fun _ => C) (F.R 132) := by simpa using haccuracy
  exact ⟨v',F,1+m,E',hu',by dsimp only [keys] at hm; omega,Exec.seq hpeek he,h93,hi,ho,hrdy,hqueue,hzero,hframe,hall,
    haloInterior_error_of_packed_reads hst hab hb C (F.R 132) hall x hx,hrange,hwords,hleftAll⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
