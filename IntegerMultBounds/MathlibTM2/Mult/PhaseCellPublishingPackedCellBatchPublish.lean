module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishingPackedCellBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCellPublish
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCellPublishedAccuracy

/-! Execute local gathering, cell arithmetic and publication with one generated
advance schedule. The destination and preserved dimensions are caller-owned. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

noncomputable def publishingPackedCellBatchPublish (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 168 Q A U :=
  .seq (publishingPackedCellBatch hR hQ) packedCellPublish

theorem publishingPackedCellBatchPublish_sized_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (E outputTail : List (Fin (A+4)))
    (hE : E.length = N*executionWidth p l target rhsExp)
    (h128 : (S.R 128).length = L)
    (h130 : (S.R 130).length = executionWidth p l target rhsExp)
    (h132 : S.R 132 = E++outputTail) (h140 : S.R 140 = [])
    (hprotected : ∀ k ∈ [(131 : Fin 168),134,135], S.R k = [])
    (h165 : S.R 165 = binSyms V N) (h166 : S.R 166 = []) (hV : (S.R 163).length = V)
    (h153 : S.R 153 = []) (h155 : S.R 155 = binSyms V origin) (h154 : S.R 154 = binSyms V 0) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let j := executionStagePrecision p l target rhsExp
    let cExp := sourceExponent l target rhsExp
    let lo := packedCellOrigin (s := s) origin offsets
    let ys := cstream A w (publishedWords offsets.length L
      (executedOutputWords s t p u q l offsets.length L j cExp lo (fun _ => C)))
    ∃ v' F m, v'.user = v.user ∧
      m ≤ packedCellGroupInputCost V N L w offsets.length q+
        (12*N*w+21*offsets.length+6*L*w+9*L+27)+
        sizedClosedBatchCost p l offsets.length L s t u target rhsExp+(54*N*w+15) ∧
      Exec body (publishingPackedCellBatchPublish hR hQ) (mk v S) m (mk v' F) ∧
      F.R 93 = outTail ∧ F.R 140 = [] ∧
      F.R 132 = scatterRows (L*w) E ys (packedCellGaps L w offsets)++outputTail ∧
      embStk packedCellCoreReg F = releasedCellBank
        (cstream A w ((List.range offsets.length).flatMap (cellSourceRows L lo (fun _ => C))))
        (cstream A w (packedInterval origin N C)++tail) outTail inp out ∧
      (∀ k : Fin 168, 117 ≤ k.val → k ≠ 132 → F.L k = S.L k ∧ F.R k = S.R k) ∧
      PackedCellOutputSpec t p u l target rhsExp L offsets lo (fun _ => C) (F.R 132) ∧
      (∀ n : Fin offsets.length,
        (executedRun s t p u q l w offsets.length L j cExp lo (fun _ => C) n outTail).Valid
          s t p u (lo n) L (fun k => (value q (C k)).re)
          (1/(2 : ℝ)^j) ((2 : ℝ)^inputExponent p cExp)) ∧ F.L = S.L := by
  dsimp only
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let lo := packedCellOrigin (s := s) origin offsets
  let ys := cstream A w (publishedWords offsets.length L
    (executedOutputWords s t p u q l offsets.length L
      (executionStagePrecision p l target rhsExp) (sourceExponent l target rhsExp) lo (fun _ => C)))
  obtain ⟨v₁,F,m₁,hu₁,hm₁,he₁,hproj,hframe,hcontrols,hvalid⟩ := publishingPackedCellBatch_sized_exec
    (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget hL hLs hpad C hC offsets hne hdis
    hhalo hfit hVeq hwV hcoords hunits tail outTail inp out v S hbank hprotected
    h165 h166 hV h153 h155 h154
  have hRnative (k : Fin 117) := congrArg (fun B : Stacks 117 A => B.R k) hproj
  have hys : ys.length = offsets.length*(L*w) := by
    simp [ys,publishedWords_length,executedOutputWords_length,Nat.mul_assoc]
  have hclean : ∀ k ∈ [(88 : Fin 168),89,90,92,94,131,134,135], F.R k = [] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
    | simpa [embStk,packedCellCoreReg,releasedCellBank] using hRnative 88
    | simpa [embStk,packedCellCoreReg,releasedCellBank] using hRnative 89
    | simpa [embStk,packedCellCoreReg,releasedCellBank] using hRnative 90
    | simpa [embStk,packedCellCoreReg,releasedCellBank] using hRnative 92
    | simpa [embStk,packedCellCoreReg,releasedCellBank] using hRnative 94
    | exact ((hframe 131 (by decide)).2 (by decide)).trans (hprotected 131 (by simp))
    | exact ((hframe 134 (by decide)).2 (by decide)).trans (hprotected 134 (by simp))
    | exact ((hframe 135 (by decide)).2 (by decide)).trans (hprotected 135 (by simp))
  have hwpos : 1 ≤ w := by dsimp [w,executionWidth]; omega
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := packedCellPublish_exec (body := body) N L w (by omega) hwpos
    offsets hne hdis hfit E ys outTail outputTail hE hys v₁ F
    (by simpa [((hframe 128 (by decide)).2 (by decide))] using h128)
    (by simpa [((hframe 130 (by decide)).2 (by decide))] using h130)
    (by simpa only [h140,List.append_nil] using hcontrols)
    (((hframe 132 (by decide)).2 (by decide)).trans h132)
    (by simpa [embStk,packedCellCoreReg,releasedCellBank,ys,q,w,lo] using hRnative 93) hclean
  let G : Stacks 168 A := {F with R := (Function.update (Function.update (Function.update F.R 93 outTail)
    132 (scatterRows (L*w) E ys (packedCellGaps L w offsets)++outputTail)) 140 [])}
  have hacc : PackedCellOutputSpec t p u l target rhsExp L offsets lo (fun _ => C) (G.R 132) := by
    intro n I x hx hcellfit hint hcell hmax i
    apply packedPublishedCell_accuracy (by omega) hp hst hu hαu hθ hgap hbudget hL hpad lo
      (fun _ => C) offsets hdis hfit (fun _ _ k => hC k) n I x hx hcellfit hint hcell hmax i
      E outputTail (G.R 132) hE
    simp [G,ys,q,w,lo]
  have hprojG : embStk packedCellCoreReg G = releasedCellBank
      (cstream A w ((List.range offsets.length).flatMap (cellSourceRows L lo (fun _ => C))))
      (cstream A w (packedInterval origin N C)++tail) outTail inp out := by
    have hinp := congrArg (fun B : Stacks 117 A => B.inp) hproj
    have hout := congrArg (fun B : Stacks 117 A => B.out) hproj
    refine Stacks.ext hinp hout ?_ ?_
    · funext k
      simpa [embStk,G,releasedCellBank] using congrArg (fun B : Stacks 117 A => B.L k) hproj
    · funext k
      have h132 : k.val ≠ 132 := by omega
      have h140 : k.val ≠ 140 := by omega
      have hh := hRnative k
      by_cases h93 : k.val = 93
      · simp [embStk,G,packedCellCoreReg,Fin.ext_iff,h132,h140,h93,releasedCellBank]
      · simpa [embStk,G,packedCellCoreReg,Fin.ext_iff,h132,h140,h93,releasedCellBank] using hh
  have hframeG : ∀ k : Fin 168, 117 ≤ k.val → k ≠ 132 → G.L k = S.L k ∧ G.R k = S.R k := by
    intro k hk hn132
    have hh := hframe k hk
    refine ⟨hh.1,?_⟩
    by_cases hn140 : k = 140
    · subst k; simp [G,h140]
    · have hn93 : k ≠ 93 := by intro he; subst k; norm_num at hk
      simpa [G,hn132,hn140,hn93] using hh.2 hn140
  have hleftAll : G.L = S.L := by
    apply packedCell_left_eq
    · intro i
      have hF : G.L (packedCellCoreReg i) = [] := by
        simpa [embStk,releasedCellBank] using congrArg (fun B : Stacks 117 A => B.L i) hprojG
      have hS : S.L (packedCellCoreReg i) = [] := by
        simpa [embStk,batchInputBank] using congrArg (fun B : Stacks 117 A => B.L i) hbank
      exact hF.trans hS.symm
    · intro k hk
      exact (hframe k hk).1
  exact ⟨v₂,G,m₁+m₂,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,Exec.seq he₁ he₂,
    by simp [G],by simp [G],by simp [G,ys,q,w,lo],hprojG,hframeG,hacc,hvalid,hleftAll⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
