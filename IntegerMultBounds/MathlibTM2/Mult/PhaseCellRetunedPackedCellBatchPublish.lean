module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReusablePackedCellBatchPublish
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplaceUnary

/-! Retune only the cell-length dimension before publishing the next group into
an existing packed buffer. The common word width and source remain retained. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

noncomputable def retunedPackedCellBatchPublish (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 168 Q A U :=
  .seq (replaceUnary 102 128 104) (reusablePackedCellBatchPublish hR hQ)

theorem retunedPackedCellBatchPublish_sized_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (h129 : S.R 129 = [])
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
      m ≤ (2*(S.R 128).length+4*L+6)+reusablePackedCellBatchPublishCost p l target rhsExp V N L offsets.length s t u ∧
      Exec body (retunedPackedCellBatchPublish hR hQ) (mk v S) m (mk v' F) ∧
      F.R 93 = outTail ∧ F.R 140 = [] ∧ F.R 128 = List.replicate L tick ∧
      F.R 132 = scatterRows (L*w) E ys (packedCellGaps L w offsets)++outputTail ∧
      embStk packedCellCoreReg F = releasedCellBank []
        (cstream A w (packedInterval origin N C)++tail) outTail inp out ∧
      (∀ k : Fin 168, 117 ≤ k.val → k ≠ 128 → k ≠ 132 → F.L k = S.L k ∧ F.R k = S.R k) ∧
      PackedCellOutputSpec t p u l target rhsExp L offsets lo (fun _ => C) (F.R 132) ∧
      ∀ n : Fin offsets.length,
        (executedRun s t p u q l w offsets.length L j cExp lo (fun _ => C) n outTail).Valid
          s t p u (lo n) L (fun k => (value q (C k)).re)
          (1/(2 : ℝ)^j) ((2 : ℝ)^inputExponent p cExp) := by
  dsimp only
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let lo := packedCellOrigin (s := s) origin offsets
  let ys := cstream A w (publishedWords offsets.length L
    (executedOutputWords s t p u q l offsets.length L
      (executionStagePrecision p l target rhsExp) (sourceExponent l target rhsExp) lo (fun _ => C)))
  have h104 : S.R 104 = [] := by
    simpa [embStk,packedCellCoreReg,batchInputBank] using
      congrArg (fun B : Stacks 117 A => B.R 104) hbank
  have h102 : (S.R 102).length = L := by
    have hh : S.R 102 = List.replicate L tick := by
      simpa [embStk,packedCellCoreReg,batchInputBank] using
        congrArg (fun B : Stacks 117 A => B.R 102) hbank
    simp only [hh,List.length_replicate]
  obtain ⟨v₀,hu₀,he₀⟩ := replaceUnary_exec (body := body)
    (src := 102) (dst := 128) (tmp := 104) (by decide) v S h104
  let S₀ : Stacks 168 A := {S with R := Function.update S.R 128 (List.replicate L tick)}
  have he₀' : Exec body (replaceUnary 102 128 104) (mk v S) (2*(S.R 128).length+4*L+6) (mk v₀ S₀) := by
    simpa only [h102] using he₀
  have hcore : embStk packedCellCoreReg S₀ = embStk packedCellCoreReg S := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    have hk : packedCellCoreReg k ≠ 128 := by
      intro he; have hh := congrArg Fin.val he; have hk := k.isLt
      change k.val = 128 at hh; omega
    simp [S₀,embStk,hk]
  obtain ⟨v₁,F,m₁,hu₁,hm₁,he₁,h93,h140F,houtput,hproj,hframe,hacc,hvalid,_hleftAll⟩ :=
    reusablePackedCellBatchPublish_sized_exec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget
      hL hLs hpad C hC offsets hne hdis hhalo hfit hVeq hwV hcoords hunits tail outTail inp out v₀ S₀
      (hcore.trans hbank) E outputTail hE (by simpa [S₀] using h129) (by simp [S₀])
      (by simpa [S₀] using h130) (by simpa [S₀] using h132) (by simpa [S₀] using h140) (by
        intro k hk
        have hn : k ≠ 128 := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl <;> decide
        simpa [S₀,hn] using hprotected k hk)
      (by simpa [S₀] using h165) (by simpa [S₀] using h166) (by simpa [S₀] using hV)
      (by simpa [S₀] using h153) (by simpa [S₀] using h155) (by simpa [S₀] using h154)
  have hframeF : ∀ k : Fin 168, 117 ≤ k.val → k ≠ 128 → k ≠ 132 → F.L k = S.L k ∧ F.R k = S.R k := by
    intro k hk hn128 hn132
    simpa [S₀,hn128] using hframe k hk hn132
  refine ⟨v₁,F,(2*(S.R 128).length+4*L+6)+m₁,hu₁.trans hu₀,Nat.add_le_add_left hm₁ _,
    Exec.seq he₀' he₁,h93,h140F,?_,?_,hproj,hframeF,hacc,hvalid⟩
  · have hh := (hframe 128 (by decide) (by decide)).2
    simpa [S₀] using hh
  · simpa [S₀] using houtput

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
