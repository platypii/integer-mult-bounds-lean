module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedPackedCellBatchPublish
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreservePackedRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareSharedCouplingRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedCouplingHeaders

/-! The executed interior stage preserves the original local RHS, publishes its
solution and presents the shared-header readiness needed by residual coupling. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def residualReadyPackedCellBatchCost (p l target rhsExp V N L K s t u : ℕ) : ℕ :=
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  (16*N*w+17*N+11*V+8*q+2*w+36)+((16*N*w+17*N+11*V+8*q+4*L+37)+(packedCellGroupInputCost V N L w K q+
        (12*N*w+21*K+6*L*w+9*L+27)+
        sizedClosedBatchCost p l K L s t u target rhsExp+(54*N*w+15)))+(4*PhaseCellBand.width p u+5)

noncomputable def residualReadyPackedCellBatch (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 168 Q A U :=
  .seq preservePackedRhs (.seq (generatedPackedCellBatchPublish hR hQ) prepareSharedCouplingRows)

theorem residualReadyPackedCellBatch_sized_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l L s t p u target rhsExp origin N V : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hL : 0 < L) (hLs : L ≤ s) (hpad : L+L ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (offsets : List ℕ) (hne : offsets ≠ []) (hdis : offsets.Pairwise (fun i j => i+L ≤ j))
    (hhalo : origin+N ≤ s) (hfit : ∀ j ∈ offsets, j+L ≤ N)
    (hVeq : V = weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (2*executionPrecision p l target rhsExp+8) t u)
    (hwV : executionWidth p l target rhsExp < 2^V)
    (hcoords : origin+N < 2^V) (hunits : (origin+N)*executionWidth p l target rhsExp < 2^V)
    (tail outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hbank : embStk packedCellCoreReg S = batchInputBank (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) L offsets.length
      (fun i => (packedCellOrigin (s := s) origin offsets i).val) []
      (cstream A (executionWidth p l target rhsExp) (packedInterval origin N C)++tail) outTail inp out)
    (hPmaster : (S.R 117).length = 2^15*p)
    (hqmaster : (S.R 119).length = executionPrecision p l target rhsExp)
    (hsmaster : (S.R 121).length = s) (htmaster : (S.R 122).length = t)
    (humaster : (S.R 123).length = u) (hbandmaster : (S.R 124).length = PhaseCellBand.width p u)
    (hamaster : (S.R 141).length = origin) (hbmaster : (S.R 142).length = origin+N)
    (hleft : ∀ k ∈ [(121 : Fin 168),122,123,124], S.L k = [])
    (hpublication : ∀ k ∈ [(128 : Fin 168),130,131,134,135,140], S.R k = [])
    (h165 : S.R 165 = binSyms V N) (h166 : S.R 166 = []) (hV : (S.R 163).length = V)
    (h153 : S.R 153 = []) (h155 : S.R 155 = binSyms V origin) (h154 : S.R 154 = binSyms V 0) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let j := executionStagePrecision p l target rhsExp
    let cExp := sourceExponent l target rhsExp
    let lo := packedCellOrigin (s := s) origin offsets
    let words := scatterRows L (packedInterval origin N C)
      (publishedWords offsets.length L
        (executedOutputWords s t p u q l offsets.length L j cExp lo (fun _ => C)))
      (windowGaps L 0 offsets)
    let D := packedField (s := s) origin words
    let E := cstream A w (packedInterval origin N C)
    ∃ v' F m, v'.user = v.user ∧
      m ≤ residualReadyPackedCellBatchCost p l target rhsExp V N L offsets.length s t u ∧
      Exec body (residualReadyPackedCellBatch hR hQ) (mk v S) m (mk v' F) ∧
      F.R 93 = E++outTail ∧ F.R 140 = List.replicate (2*PhaseCellBand.width p u+1) tick ∧
      F.R 132 = cstream A w (packedInterval origin N D)++S.R 132 ∧
      (∀ k, ‖value q (D k)‖ ≤ (2 : ℝ)^interiorOutputExponent p l target rhsExp) ∧
      (∀ k, Fits w (D k)) ∧
      embStk packedCellCoreReg F = releasedCellBank
        (cstream A w ((List.range offsets.length).flatMap (cellSourceRows L lo (fun _ => C))))
        (cstream A w (packedInterval origin N C)++tail) (E++outTail) inp out ∧
      (∀ k : Fin 168, 117 ≤ k.val → k ≠ 128 → k ≠ 130 → k ≠ 132 → k ≠ 140 →
        F.L k = S.L k ∧ F.R k = S.R k) ∧
      F.R 128 = List.replicate L tick ∧ F.R 130 = List.replicate w tick ∧
      CouplingReady (2^15*p) q w s t u (PhaseCellBand.width p u) origin (origin+N)
        (cstream A w ((List.range offsets.length).flatMap (cellSourceRows L lo (fun _ => C)))++(E++tail))
        (embStk sharedCouplingCoreReg F) ∧
      PackedCellOutputSpec t p u l target rhsExp L offsets lo (fun _ => C) (F.R 132) ∧
      ∀ n : Fin offsets.length,
        (executedRun s t p u q l w offsets.length L j cExp lo (fun _ => C) n (E++outTail)).Valid
          s t p u (lo n) L (fun k => (value q (C k)).re)
          (1/(2 : ℝ)^j) ((2 : ℝ)^inputExponent p cExp) := by
  dsimp only
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let E := cstream A w (packedInterval origin N C)
  let lo := packedCellOrigin (s := s) origin offsets
  let rhs := cstream A w ((List.range offsets.length).flatMap (cellSourceRows L lo (fun _ => C)))
  have hw : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  have hnative (k : Fin 117) := congrArg (fun B : Stacks 117 A => B.R k) hbank
  have hclean : ∀ k ∈ [(0 : Fin 168),1,2,94,104,105,108,166], S.R k = [] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
    | simpa [embStk,packedCellCoreReg,batchInputBank] using hnative 0
    | simpa [embStk,packedCellCoreReg,batchInputBank] using hnative 1
    | simpa [embStk,packedCellCoreReg,batchInputBank] using hnative 2
    | simpa [embStk,packedCellCoreReg,batchInputBank] using hnative 94
    | simpa [embStk,packedCellCoreReg,batchInputBank] using hnative 104
    | simpa [embStk,packedCellCoreReg,batchInputBank] using hnative 105
    | simpa [embStk,packedCellCoreReg,batchInputBank] using hnative 108
    | exact h166
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := preservePackedRhs_exec (body := body) V N q w (by omega) hw E tail
    (by simp [E,packedInterval_length C hhalo]) v S
    (by simpa [embStk,packedCellCoreReg,batchInputBank,q] using congrArg List.length (hnative 112))
    h165 (by simpa [embStk,packedCellCoreReg,batchInputBank,E,w] using hnative 110) hclean
  let G : Stacks 168 A := {S with R := Function.update S.R 93 (E++S.R 93)}
  have h93 : S.R 93 = outTail := by simpa [embStk,packedCellCoreReg,batchInputBank] using hnative 93
  have hbankG : embStk packedCellCoreReg G = batchInputBank (2^15*p)
      (executionStagePrecision p l target rhsExp+1) q l s t u (PhaseCellBand.width p u) L offsets.length
      (fun i => (lo i).val) [] (E++tail) (E++outTail) inp out := by
    have hproj : embStk packedCellCoreReg G = {embStk packedCellCoreReg S with
        R := Function.update (embStk packedCellCoreReg S).R 93 (E++S.R 93)} := by
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      simp [G,embStk,packedCellCoreReg,Function.update_apply,Fin.ext_iff]
    rw [hproj,hbank,h93]
    exact batchInputBank_update_result _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hpubG : ∀ k ∈ [(128 : Fin 168),130,131,134,135,140], G.R k = [] := by
    intro k hk
    have hn : k ≠ 93 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [G,hn] using hpublication k hk
  obtain ⟨v₂,F,m₂,hu₂,hm₂,he₂,h93F,h140F,houtput,hDnorm,hDfits,hproj,hframe,h128,h130,hacc,hvalid⟩ :=
    generatedPackedCellBatchPublish_sized_exec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget
      hL hLs hpad C hC offsets hne hdis hhalo hfit hVeq hwV hcoords hunits tail (E++outTail) inp out v₁ G
      hbankG hpubG (by simpa [G] using h165) (by simpa [G] using h166) (by simpa [G] using hV)
      (by simpa [G] using h153) (by simpa [G] using h155) (by simpa [G] using h154)
  have hbandF : (F.R 124).length = PhaseCellBand.width p u := by
    rw [(hframe 124 (by decide) (by decide) (by decide) (by decide)).2]
    simpa [G] using hbandmaster
  have h135F : F.R 135 = [] := by
    rw [(hframe 135 (by decide) (by decide) (by decide) (by decide)).2]
    simpa [G] using hpublication 135 (by simp)
  obtain ⟨v₃,hu₃,he₃⟩ := prepareSharedCouplingRows_exec (body := body)
    (PhaseCellBand.width p u) v₂ F hbandF h140F h135F
  let H : Stacks 168 A := {F with R := Function.update F.R 140 (List.replicate (2*PhaseCellBand.width p u+1) tick)}
  have hprojH : embStk packedCellCoreReg H = releasedCellBank rhs (E++tail) (E++outTail) inp out := by
    have heq : embStk packedCellCoreReg H = embStk packedCellCoreReg F := by
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      have hn : packedCellCoreReg k ≠ 140 := by
        intro he
        have hv := congrArg (fun j : Fin 168 => j.val) he
        have hk := k.isLt
        change k.val = 140 at hv
        omega
      simp only [H,embStk,Function.comp_apply,Function.update_of_ne hn]
    rw [heq]
    exact hproj
  have hframeH : ∀ k : Fin 168, 117 ≤ k.val → k ≠ 128 → k ≠ 130 → k ≠ 132 → k ≠ 140 →
      H.L k = S.L k ∧ H.R k = S.R k := by
    intro k hk hn128 hn130 hn132 hn140
    have hh := hframe k hk hn128 hn130 hn132
    have hn93 : k ≠ 93 := by intro he; subst k; norm_num at hk
    simpa [H,G,hn140,hn93] using hh
  have hwidthH : H.R 130 = List.replicate w tick := by simpa [H] using h130
  have hreadyH : CouplingReady (2^15*p) q w s t u (PhaseCellBand.width p u) origin (origin+N)
      (rhs++(E++tail)) (embStk sharedCouplingCoreReg H) := by
    apply sharedCouplingHeaders_ready H rhs (E++tail) (E++outTail) inp out hprojH
    · rw [(hframeH 117 (by decide) (by decide) (by decide) (by decide) (by decide)).2]; exact hPmaster
    · rw [(hframeH 119 (by decide) (by decide) (by decide) (by decide) (by decide)).2]; exact hqmaster
    · rw [(hframeH 121 (by decide) (by decide) (by decide) (by decide) (by decide)).2]; exact hsmaster
    · rw [(hframeH 122 (by decide) (by decide) (by decide) (by decide) (by decide)).2]; exact htmaster
    · rw [(hframeH 123 (by decide) (by decide) (by decide) (by decide) (by decide)).2]; exact humaster
    · rw [(hframeH 124 (by decide) (by decide) (by decide) (by decide) (by decide)).2]; exact hbandmaster
    · rw [(hframeH 141 (by decide) (by decide) (by decide) (by decide) (by decide)).2]; exact hamaster
    · rw [(hframeH 142 (by decide) (by decide) (by decide) (by decide) (by decide)).2]; exact hbmaster
    · rw [hwidthH]; simp
    · intro k hk
      have hgood : 117 ≤ k.val ∧ k ≠ 128 ∧ k ≠ 130 ∧ k ≠ 132 ∧ k ≠ 140 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl <;> decide
      rw [(hframeH k hgood.1 hgood.2.1 hgood.2.2.1 hgood.2.2.2.1 hgood.2.2.2.2).1]
      exact hleft k hk
  refine ⟨v₃,H,m₁+(m₂+(4*PhaseCellBand.width p u+5)),hu₃.trans (hu₂.trans hu₁),(by dsimp only [residualReadyPackedCellBatchCost,q,w] at hm₁ ⊢; omega),
    Exec.seq he₁ (Exec.seq he₂ he₃),?_,by simp [H],?_,hDnorm,hDfits,hprojH,hframeH,
    by simpa [H] using h128,hwidthH,hreadyH,?_,hvalid⟩
  · simpa [H] using h93F
  · simpa [H,G] using houtput
  · simpa [H] using hacc

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
