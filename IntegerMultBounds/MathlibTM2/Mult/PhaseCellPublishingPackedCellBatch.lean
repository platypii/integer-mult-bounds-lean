module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishingPackedCellInputBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedBatchExec

/-! Generate the shared gather/publication schedule and execute the unchanged
closed arithmetic batch. Publication controls survive outside the native bank;
validity concerns the actual returned words of this same execution. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

noncomputable def publishingPackedCellBatch (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 168 Q A U :=
  .seq rawPublishingPackedCellInputs (embProg packedCellCoreReg Empty.elim (closedBatch (P₀ := Empty) hR hQ))

theorem publishingPackedCellBatch_sized_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (hprotected : ∀ k ∈ [(131 : Fin 168),134,135], S.R k = [])
    (h165 : S.R 165 = binSyms V N) (h166 : S.R 166 = []) (hV : (S.R 163).length = V)
    (h153 : S.R 153 = []) (h155 : S.R 155 = binSyms V origin) (h154 : S.R 154 = binSyms V 0) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let j := executionStagePrecision p l target rhsExp
    let cExp := sourceExponent l target rhsExp
    let lo := packedCellOrigin (s := s) origin offsets
    let rhs := cstream A w ((List.range offsets.length).flatMap (cellSourceRows L lo (fun _ => C)))
    ∃ v' F m, v'.user = v.user ∧
      m ≤ packedCellGroupInputCost V N L w offsets.length q+
        (12*N*w+21*offsets.length+6*L*w+9*L+27)+
        sizedClosedBatchCost p l offsets.length L s t u target rhsExp ∧
      Exec body (publishingPackedCellBatch hR hQ) (mk v S) m (mk v' F) ∧
      embStk packedCellCoreReg F = releasedCellBank rhs
        (cstream A w (packedInterval origin N C)++tail)
        (cstream A w (publishedWords offsets.length L
          (executedOutputWords s t p u q l offsets.length L j cExp lo (fun _ => C)))++outTail) inp out ∧
      (∀ k : Fin 168, 117 ≤ k.val → F.L k = S.L k ∧ (k ≠ 140 → F.R k = S.R k)) ∧
      F.R 140 = gatherControls A (packedCellGaps L w offsets)++S.R 140 ∧
      ∀ n : Fin offsets.length,
        (executedRun s t p u q l w offsets.length L j cExp lo (fun _ => C) n outTail).Valid
          s t p u (lo n) L (fun k => (value q (C k)).re)
          (1/(2 : ℝ)^j) ((2 : ℝ)^inputExponent p cExp) := by
  dsimp only
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let lo := packedCellOrigin (s := s) origin offsets
  let rhs := cstream A w ((List.range offsets.length).flatMap (cellSourceRows L lo (fun _ => C)))
  have hw : executionWidth p l target rhsExp = 2*executionPrecision p l target rhsExp+8 := by
    dsimp [executionWidth,executionPrecision]
    omega
  have hbank' : embStk packedCellCoreReg S = batchInputBank (2^15*p) (executionStagePrecision p l target rhsExp+1)
      q l s t u (PhaseCellBand.width p u) L offsets.length (fun i => (lo i).val) []
      (cstream A (2*q+8) (packedInterval origin N C)++tail) outTail inp out := by
    simpa only [hw] using hbank
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁,hinput⟩ := publishingPackedCellInputBank_exec (body := body)
    C hhalo hL offsets hne hdis hfit hVeq (by simpa only [hw] using hwV) hcoords
    (by simpa only [hw] using hunits) tail outTail inp out v S hbank'
    hprotected h165 h166 hV h153 h155 h154
  let G : Stacks 168 A := {S with R := (Function.update (Function.update S.R 140
    (gatherControls A (packedCellGaps L w offsets)++S.R 140)) 110 (rhs++S.R 110))}
  have he₁' : Exec body rawPublishingPackedCellInputs (mk v S) m₁ (mk v₁ G) := by
    simpa only [G,rhs,lo,w,q,hw] using he₁
  obtain ⟨vi,m₂,hui,hm₂,hei,hvalid⟩ := closedBatch_sized_exec (body := fun p : Empty => nomatch p)
    hR hQ hA hp hst hu hαu hθ hgap hbudget hL hLs hpad lo (fun _ => C)
    (fun _ _ k => hC k) (embDn packedCellCoreReg v₁) outTail
    (cstream A w (packedInterval origin N C)++tail) inp out
  obtain ⟨v₂,F,he₂,hv₂,hu₂,hproj,hframe⟩ := exec_emb (body' := body) (ι := Empty.elim)
    packedCellCoreReg_injective (fun p => nomatch p) hei v₁ rfl G
    (by simpa only [G,rhs,lo,w,q,hw] using hinput)
  refine ⟨v₂,F,m₁+m₂,hu₂.trans (hui.trans hu₁),Nat.add_le_add (by simpa only [w,q,hw] using hm₁) hm₂,
    Exec.seq he₁' he₂,hproj,?_,?_,hvalid⟩
  · intro k hk
    have hoff : ∀ i, packedCellCoreReg i ≠ k := by
      intro i he
      have hv := congrArg (fun r : Fin 168 => r.val) he
      have hi := i.isLt
      change i.val = k.val at hv
      omega
    have hh := hframe k hoff
    have hn110 : k ≠ 110 := by intro he; subst k; norm_num at hk
    refine ⟨by simpa [G] using hh.1,?_⟩
    intro hn140
    simpa [G,hn110,hn140] using hh.2
  · have hoff : ∀ i, packedCellCoreReg i ≠ (140 : Fin 168) := by
      intro i he
      have hv := congrArg (fun r : Fin 168 => r.val) he
      have hi := i.isLt
      change i.val = 140 at hv
      omega
    simpa [G] using (hframe 140 hoff).2

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
