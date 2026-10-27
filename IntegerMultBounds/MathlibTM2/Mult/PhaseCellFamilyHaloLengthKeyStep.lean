module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyLengthKeyFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloLengthKeyStep

/-! One numerical counted step selects the matching retained page, executes the
class, and preserves every other class's published reads. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 151 Q A U}

theorem familyHaloLengthKeyStep_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l L s t p u target rhsExp V a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hpad : L+L ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re))
    (v : HS 151 Q A U) (S : Stacks 151 A) (borrowed E outputTail keyTail familyTail : List (Fin (A+4)))
    (c : Fin (A+4)) (cs : List (Fin (A+4))) (hcount : S.R 127 = c::cs)
    (hkey : L < 2^V) (hkeys : S.R 126 = binSyms V L++keyTail)
    (hE : E.length = s*executionWidth p l target rhsExp) (hdst : S.R 132 = E++outputTail)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) V
      (executionWidth p l target rhsExp) (cstream A (executionWidth p l target rhsExp) (chirpLine s C)++borrowed)
      (weightFamilyLegacyBank S))
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hfamily : S.R 148 = weightKeyPacket (batchWeightPage A (executionWidth p l target rhsExp)
      (executionPrecision p l target rhsExp) (2^15*p) s t u
      (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length L
      (fun n => (haloGroupOrigin s t (PhaseCellBand.width p u) a b L n).val))++familyTail)
    (hcacheFresh : ∀ i ∈ ([(144 : Fin 151),145,146,147,149] : List (Fin 151)), S.R i = []) :
    let band := PhaseCellBand.width p u
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    ∃ v' S' n, ∃ E' : List (Fin (A+4)), v'.user = v.user ∧ v'.flag = cs.head?.isSome ∧
      n ≤ familyProcessHaloLengthKeyCost p l L s t u target rhsExp V a b+2 ∧
      Exec body (familyHaloLengthKeyStep hR hQ) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ E'.length = s*w ∧
      (weightFamilyLegacyBank S').R = keyLoopR (weightFamilyLegacyBank S).R keyTail cs (E'++outputTail) ∧
      S'.R 148 = familyTail ∧
      S'.R 150 = (weightKeyPacket (batchWeightPage A w q (2^15*p) s t u
        (haloLengthGroup s t band a b L).length L
        (fun n => (haloGroupOrigin s t band a b L n).val))).reverse++S.R 150 ∧
      (∀ i ∈ ([(144 : Fin 151),145,146,147,149] : List (Fin 151)), S'.R i = []) ∧
      (∀ n : Fin (haloLengthGroup s t band a b L).length,
        PhaseCellInterface.ErrorOn (publishedCellCore (haloGroupOrigin s t band a b L n) L)
          (publishedCellRead q w (0 : ZMod s) (S'.R 132)) x (1/(2 : ℝ)^target)) ∧
      (∀ K, K ≠ L → ∀ n : Fin (haloLengthGroup s t band a b K).length, ∀ j ∈ publishedCellCore
        (haloGroupOrigin s t band a b K n) K,
        publishedCellRead q w (0 : ZMod s) (S'.R 132) j = publishedCellRead q w (0 : ZMod s) (S.R 132) j) ∧
      (EncodedRange A w q (interiorOutputExponent p l target rhsExp) E →
        EncodedRange A w q (interiorOutputExponent p l target rhsExp) E') := by
  dsimp only
  let band := PhaseCellBand.width p u
  let B := (haloLengthGroup s t band a b L).length
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let S₀ : Stacks 151 A := {S with R := Function.update S.R 127 cs}
  have hr := hready.pop_family cs
  change LengthKeyReady _ _ _ _ _ _ _ _ _ _ _ (weightFamilyLegacyBank S₀) at hr
  obtain ⟨v₁,S₁,n₁,ys,hu₁,hn₁,he₁,hi₁,ho₁,hl₁,hylen,hframe,hs,hc,hfresh,herror⟩ :=
    familyProcessHaloLengthKey_spec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget hband has hbs hL hLs hpad C hC x hx
      v S₀ borrowed E outputTail keyTail familyTail hkey hr.keyWidth
      (by simpa [S₀,embStk,weightFamilyCoreReg] using hkeys) hE
      (by simpa [S₀,embStk,weightFamilyCoreReg] using hdst) hr.masters
      (by simpa [S₀,embStk,weightFamilyCoreReg] using haMaster)
      (by simpa [S₀,embStk,weightFamilyCoreReg] using hbMaster) (by
        intro k hk
        simpa [weightFamilyLegacyBank,embStk,cachedGroupLegacyReg,weightFamilyCoreReg] using
          hr.left ⟨k.val,by omega⟩ hk) (by
        intro k hk hk93 hk110
        simpa [weightFamilyLegacyBank,embStk,cachedGroupLegacyReg,weightFamilyCoreReg] using
          hr.blank ⟨k.val,by omega⟩ hk
            (by simpa [Fin.ext_iff] using hk93) (by simpa [Fin.ext_iff] using hk110))
      hr.source hr.countSaved hr.headerTemp hr.wordWidth (by
        intro k hk
        have hk144 : k.val < 144 := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        simpa [weightFamilyLegacyBank,embStk,cachedGroupLegacyReg,weightFamilyCoreReg] using
          hr.fresh ⟨k.val,hk144⟩ (by simpa [Fin.ext_iff] using hk))
      (by simpa [S₀] using hfamily) (by
        intro i hi
        have hi127 : i ≠ 127 := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
        simpa [S₀,hi127] using hcacheFresh i hi)
  have h128 : (weightFamilyLegacyBank S).R 128 = [] := by
    have hh := hready.masters (128,102) (by simp [groupHeaderCopies])
    exact List.eq_nil_of_length_eq_zero (by simpa [groupHeaderValue] using hh)
  let E' := scatterRows (L*w) E (ys++S.R 93) (haloScatterGaps s t band a b L w)
  have hframe' : (weightFamilyLegacyBank S₁).R =
      keyLoopR (weightFamilyLegacyBank S).R keyTail cs (E'++outputTail) := by
    have hf := weightFamilyLegacyBank_published S₀ S₁ keyTail (E'++outputTail) hframe
    rw [weightFamilyLegacyBank_pop] at hf
    exact hf.trans (keyLoopR_step _ keyTail cs (E'++outputTail) h128 hready.countSaved (hready.fresh 140 (by simp)))
  have hE' : E.length = s*w := hE
  have hys : ys.val.length = B*(L*w) := by simpa only [Nat.mul_assoc] using hylen
  have hX : B*(L*w) ≤ (ys++S.R 93).length := by simp only [List.length_append]; omega
  have hf := haloScatterGaps_fits s t band a b L w E hE'.ge
  have hlen : E'.length = s*w := by
    rw [length_scatterRows (L*w) E (ys++S.R 93) (haloScatterGaps s t band a b L w) hf
      (by simpa only [haloScatterGaps_length] using hX)]
    exact hE'
  have hcount₁ : S₁.R 127 = cs := by
    simpa [keyLoopR,weightFamilyLegacyBank,embStk,cachedGroupLegacyReg,weightFamilyCoreReg] using
      congrArg (fun R => R 127) hframe'
  refine ⟨{v₁ with flag := cs.head?.isSome},S₁,n₁+2,E',hu₁,rfl,by omega,
    familyHaloLengthKeyStep_exec hR hQ v v₁ S S₁ c cs n₁ hcount hcount₁ he₁,
    hi₁,ho₁,hl₁,hlen,hframe',hs,?_,hfresh,herror,?_,?_⟩
  · simpa [S₀] using hc
  · intro K hKL n j hj
    have h132 : S₁.R 132 = E'++outputTail := by
      simpa [keyLoopR,weightFamilyLegacyBank,embStk,cachedGroupLegacyReg,weightFamilyCoreReg] using
        congrArg (fun R => R 132) hframe'
    rw [h132,hdst]
    change publishedCellRead q w (0 : ZMod s)
      (scatterRows (L*w) E (ys++S.R 93) (haloScatterGaps s t band a b L w)++outputTail) j = _
    rw [← scatterRows_append (L*w) (haloScatterGaps s t band a b L w) E (ys++S.R 93) outputTail hf]
    apply haloScatterRows_preserves_class t band a b L K q w hKL.symm (E++outputTail) (ys++S.R 93)
      (by simp only [List.length_append]; omega) hX n j hj
  · intro hBounded
    exact haloScatterRows_range s t band a b L E (S.R 93) ys hBounded hylen

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
