module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConditionalPackedHaloPublish
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellKeyedPackedHaloInput

/-! Consume one generated key, build its packed input, execute and publish the
class (including an empty candidate), then restore the borrowed source for the following key. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

noncomputable def keyedPackedHaloPublish (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 168 Q A U :=
  .seq keyedPackedHaloInput (conditionalPackedHaloPublish hR hQ)

theorem keyedPackedHaloPublish_sized_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l L s t p u target rhsExp a b V : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hL : 0 < L) (hLs : L ≤ s) (hpad : L+L ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (hab : a ≤ b) (hb : b ≤ s) (hband : PhaseCellBand.width p u ≤ s)
    (hkey : L < 2^V) (hwide : 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^V)
    (hVeq : V = weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (2*executionPrecision p l target rhsExp+8) t u)
    (hwV : executionWidth p l target rhsExp < 2^V)
    (hcoords : b < 2^V) (hunits : b*executionWidth p l target rhsExp < 2^V)
    (tail suffix : List (Fin (A+4))) (v : HS 168 Q A U) (S : Stacks 168 A)
    (hmasters : ∀ r ∈ groupHeaderCopies, r.1 ≠ 128 →
      (S.R (packedHeaderReg r.1)).length = groupHeaderValue (2^15*p)
        (executionStagePrecision p l target rhsExp+1) (executionPrecision p l target rhsExp)
        l s t u (PhaseCellBand.width p u) L r.1)
    (h133 : S.R 133 = [])
    (hleft : ∀ k : Fin 168, k.val < 117 → S.L k = [])
    (hblank : ∀ k : Fin 168, k.val < 117 → k ≠ 93 → k ≠ 110 → S.R k = [])
    (hsource : S.R 110 = cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) C)++tail)
    (hmeta : CouplingIntervalMetadata V s t (PhaseCellBand.width p u) a b a (b-a) S)
    (hwidth : (S.R 125).length = V) (hkeys : S.R 126 = binSyms V L++suffix)
    (hfresh : ∀ k ∈ [(134 : Fin 168),135,136], S.R k = [])
    (E outputTail : List (Fin (A+4))) (hE : E.length = (b-a)*executionWidth p l target rhsExp)
    (h129 : S.R 129 = []) (h130 : (S.R 130).length = executionWidth p l target rhsExp)
    (h132 : S.R 132 = E++outputTail) (h140 : S.R 140 = []) (h131 : S.R 131 = [])
    (h166 : S.R 166 = []) (h153 : S.R 153 = []) :
    let offsets := haloPackedOffsets s t (PhaseCellBand.width p u) a b L
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let j := executionStagePrecision p l target rhsExp
    let cExp := sourceExponent l target rhsExp
    let lo := packedCellOrigin (s := s) a offsets
    let ys := cstream A w (publishedWords offsets.length L
      (executedOutputWords s t p u q l offsets.length L j cExp lo (fun _ => C)))
    ∃ v' F m, v'.user = v.user ∧
      m ≤ (2*(S.R 128).length+2*(S.R 157).length+6*L+17*V+16)+
        installGroupHeadersCost (2^15*p) (executionStagePrecision p l target rhsExp+1)
          (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) L+
        binaryHaloClassCost V s t (PhaseCellBand.width p u) a b L+
        ((if offsets = [] then
          2*((2^15*p)+(executionStagePrecision p l target rhsExp+1)+q+l+s+t+u+PhaseCellBand.width p u+2*L)+21
          else reusablePackedCellBatchPublishCost p l target rhsExp V (b-a) L offsets.length s t u)+2) ∧
      Exec body (keyedPackedHaloPublish hR hQ) (mk v S) m (mk v' F) ∧
      F.R 93 = S.R 93 ∧ F.R 140 = [] ∧
      F.R 132 = scatterRows (L*w) E ys (packedCellGaps L w offsets)++outputTail ∧
      embStk packedCellCoreReg F = releasedCellBank []
        (cstream A w (packedInterval a (b-a) C)++tail) (S.R 93) S.inp S.out ∧
      (∀ k : Fin 168, 117 ≤ k.val → k ≠ 126 → k ≠ 128 → k ≠ 157 → k ≠ 132 → F.L k = S.L k ∧ F.R k = S.R k) ∧
      F.R 126 = suffix ∧ F.R 128 = List.replicate L tick ∧ F.R 157 = binSyms V L ∧
      PackedCellOutputSpec t p u l target rhsExp L offsets lo (fun _ => C) (F.R 132) ∧
      (∀ n : Fin offsets.length,
        (executedRun s t p u q l w offsets.length L j cExp lo (fun _ => C) n (S.R 93)).Valid
          s t p u (lo n) L (fun k => (value q (C k)).re)
          (1/(2 : ℝ)^j) ((2 : ℝ)^inputExponent p cExp)) ∧ F.L = S.L := by
  dsimp only
  let offsets := haloPackedOffsets s t (PhaseCellBand.width p u) a b L
  obtain ⟨v₁,B,m₁,hu₁,hm₁,he₁,hbank,h126,h128,h157,hframe,hleftInput⟩ := keyedPackedHaloInput_exec (body := body)
    hst hband hab hb hL hLs hkey (by omega) hwide hVeq _ suffix v S hmasters h133 hleft hblank
    hsource hmeta hwidth hkeys hfresh
  have hpass (k : Fin 168) (hk : 117 ≤ k.val) (h126 : k ≠ 126) (h128 : k ≠ 128) (h157 : k ≠ 157) :=
    (hframe k hk h126 h128 h157).2
  have hhalo : a+(b-a) ≤ s := by omega
  obtain ⟨v₂,F,m₂,hu₂,hm₂,he₂,h93,h140F,houtput,hproj,hframeF,hacc,hvalid,hleftPublish⟩ :=
    conditionalPackedHaloPublish_sized_exec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget
      hL hLs hpad C hC offsets (haloPackedOffsets_disjoint s t _ a b L) hhalo
      (haloPackedOffsets_fit s t _ a b L) hVeq hwV (by omega) (by simpa [Nat.add_sub_of_le hab] using hunits)
      tail (S.R 93) S.inp S.out v₁ B hbank E outputTail hE
      (by rw [hpass 129 (by decide) (by decide) (by decide) (by decide)]; exact h129)
      (by simp [h128])
      (by rw [hpass 130 (by decide) (by decide) (by decide) (by decide)]; exact h130)
      (by rw [hpass 132 (by decide) (by decide) (by decide) (by decide)]; exact h132)
      (by rw [hpass 140 (by decide) (by decide) (by decide) (by decide)]; exact h140)
      (by
        intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl
        · rw [hpass 131 (by decide) (by decide) (by decide) (by decide)]; exact h131
        · rw [hpass 134 (by decide) (by decide) (by decide) (by decide)]; exact hfresh 134 (by simp)
        · rw [hpass 135 (by decide) (by decide) (by decide) (by decide)]; exact hfresh 135 (by simp))
      (by rw [hpass 165 (by decide) (by decide) (by decide) (by decide)]; simpa [couplingIntervalValue] using hmeta.encoded 165 (by decide))
      (by rw [hpass 166 (by decide) (by decide) (by decide) (by decide)]; exact h166)
      (by rw [hpass 163 (by decide) (by decide) (by decide) (by decide)]; exact hmeta.width)
      (by rw [hpass 153 (by decide) (by decide) (by decide) (by decide)]; exact h153)
      (by rw [hpass 155 (by decide) (by decide) (by decide) (by decide)]; simpa [couplingIntervalValue] using hmeta.encoded 155 (by decide))
      (by rw [hpass 154 (by decide) (by decide) (by decide) (by decide)]; simpa [couplingIntervalValue] using hmeta.encoded 154 (by decide))
  refine ⟨v₂,F,m₁+m₂,hu₂.trans hu₁,by dsimp only [offsets] at hm₂; omega,Exec.seq he₁ he₂,h93,h140F,houtput,hproj,?_,?_,?_,?_,hacc,hvalid,hleftPublish.trans hleftInput⟩
  · intro k hk hn126 hn128 hn157 hn132
    obtain ⟨hl,hr⟩ := hframeF k hk hn132
    obtain ⟨hl',hr'⟩ := hframe k hk hn126 hn128 hn157
    exact ⟨hl.trans hl',hr.trans hr'⟩
  · exact ((hframeF 126 (by decide) (by decide)).2).trans h126
  · exact ((hframeF 128 (by decide) (by decide)).2).trans h128
  · exact ((hframeF 157 (by decide) (by decide)).2).trans h157

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
