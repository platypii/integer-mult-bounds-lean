module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishingPackedCellBatchPublish
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireProductLine

/-! Publish into a caller-owned local buffer and restore the original borrowed
source. A retained batch count pays cleanup before the next length group. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

noncomputable def reusablePackedCellBatchPublish (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 168 Q A U :=
  .seq (ucopy 116 129 104) (.seq (publishingPackedCellBatchPublish hR hQ)
    (.seq (retireProductLine 129 128 130 110 131 108 104 105) (uclear 129)))

def reusablePackedCellBatchPublishCost (p l target rhsExp V N L K s t u : ℕ) : ℕ :=
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  (4*K+4)+(packedCellGroupInputCost V N L w K q+
    (12*N*w+21*K+6*L*w+9*L+27)+sizedClosedBatchCost p l K L s t u target rhsExp+(54*N*w+15))+
    (retireProductLineCost K L w+(2*K+2))

theorem reusablePackedCellBatchPublish_sized_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
      m ≤ reusablePackedCellBatchPublishCost p l target rhsExp V N L offsets.length s t u ∧
      Exec body (reusablePackedCellBatchPublish hR hQ) (mk v S) m (mk v' F) ∧
      F.R 93 = outTail ∧ F.R 140 = [] ∧
      F.R 132 = scatterRows (L*w) E ys (packedCellGaps L w offsets)++outputTail ∧
      embStk packedCellCoreReg F = releasedCellBank []
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
  have hRnative (k : Fin 117) := congrArg (fun B : Stacks 117 A => B.R k) hbank
  have h104 : S.R 104 = [] := by simpa [embStk,packedCellCoreReg,batchInputBank] using hRnative 104
  have h116 : (S.R 116).length = offsets.length := by
    have hh : S.R 116 = List.replicate offsets.length tick := by
      simpa [embStk,packedCellCoreReg,batchInputBank] using hRnative 116
    simp only [hh,List.length_replicate]
  obtain ⟨v₀,hu₀,he₀⟩ := ucopy_exec (body := body) (a := 116) (b := 129) (t := 104)
    (by decide) (by decide) (by decide) v S h104
  let S₀ : Stacks 168 A := {S with R := Function.update S.R 129 (List.replicate offsets.length tick)}
  have he₀' : Exec body (ucopy 116 129 104) (mk v S) (4*offsets.length+4) (mk v₀ S₀) := by
    simpa [S₀,h116,h129] using he₀
  have hcore : embStk packedCellCoreReg S₀ = embStk packedCellCoreReg S := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    have hk : packedCellCoreReg k ≠ 129 := by
      intro he; have hh := congrArg Fin.val he; have hk := k.isLt
      change k.val = 129 at hh; omega
    simp [S₀,embStk,hk]
  obtain ⟨v₁,F,m₁,hu₁,hm₁,he₁,h93,h140F,houtput,hproj,hframe,hacc,hvalid,hleftAll⟩ :=
    publishingPackedCellBatchPublish_sized_exec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget
      hL hLs hpad C hC offsets hne hdis hhalo hfit hVeq hwV hcoords hunits tail outTail inp out v₀ S₀
      (hcore.trans hbank) E outputTail hE (by simpa [S₀] using h128) (by simpa [S₀] using h130)
      (by simpa [S₀] using h132) (by simpa [S₀] using h140) (by
        intro k hk
        have hn : k ≠ 129 := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl <;> decide
        simpa [S₀,hn] using hprotected k hk)
      (by simpa [S₀] using h165) (by simpa [S₀] using h166) (by simpa [S₀] using hV)
      (by simpa [S₀] using h153) (by simpa [S₀] using h155) (by simpa [S₀] using h154)
  let rhs := cstream A w ((List.range offsets.length).flatMap (cellSourceRows L lo (fun _ => C)))
  let borrowed := cstream A w (packedInterval origin N C)++tail
  have hsourceF : F.R 110 = rhs++borrowed := by
    simpa [embStk,packedCellCoreReg,releasedCellBank,rhs,borrowed,w,q,lo] using
      congrArg (fun B : Stacks 117 A => B.R 110) hproj
  have hlen : rhs.length = offsets.length*L*w := by simp [rhs,Nat.mul_assoc]
  have hcleanF (k : Fin 117) (hk : k.val ≠ 93) (hk' : k.val ≠ 110) : F.R (packedCellCoreReg k) = [] := by
    simpa [embStk,releasedCellBank,hk,hk'] using congrArg (fun B : Stacks 117 A => B.R k) hproj
  have h131F : F.R 131 = [] := by
    rw [(hframe 131 (by decide) (by decide)).2]
    simpa [S₀] using hprotected 131 (by simp)
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := retireProductLine_exec (body := body)
    129 128 130 110 131 108 104 105 (by decide) offsets.length L w rhs borrowed hlen v₁ F
    (by rw [(hframe 129 (by decide) (by decide)).2]; simp [S₀])
    (by rw [(hframe 128 (by decide) (by decide)).2]; simpa [S₀] using h128)
    (by rw [(hframe 130 (by decide) (by decide)).2]; simpa [S₀] using h130)
    hsourceF h131F (hcleanF 108 (by decide) (by decide))
    (hcleanF 104 (by decide) (by decide)) (hcleanF 105 (by decide) (by decide))
  let G : Stacks 168 A := {F with R := Function.update F.R 110 borrowed}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 129 v₂ G
  have h129G : (G.R 129).length = offsets.length := by
    simp only [G,Function.update_of_ne (by decide : (129 : Fin 168) ≠ 110)]
    rw [(hframe 129 (by decide) (by decide)).2]
    simp [S₀]
  let H : Stacks 168 A := {G with R := Function.update G.R 129 []}
  have hprojH : embStk packedCellCoreReg H = releasedCellBank [] borrowed outTail inp out := by
    have hinp := congrArg (fun B : Stacks 117 A => B.inp) hproj
    have hout := congrArg (fun B : Stacks 117 A => B.out) hproj
    refine Stacks.ext hinp hout ?_ ?_
    · funext k
      simpa [embStk,H,G,releasedCellBank] using congrArg (fun B : Stacks 117 A => B.L k) hproj
    · funext k
      have hv129 : k.val ≠ 129 := by have hk := k.isLt; omega
      by_cases h110 : k.val = 110
      · have hk : k = 110 := Fin.ext h110
        subst k; simp [embStk,H,G,packedCellCoreReg,releasedCellBank]
      · simpa [embStk,H,G,packedCellCoreReg,Function.update_apply,Fin.ext_iff,hv129,h110,releasedCellBank]
          using congrArg (fun B : Stacks 117 A => B.R k) hproj
  have hframeH : ∀ k : Fin 168, 117 ≤ k.val → k ≠ 132 → H.L k = S.L k ∧ H.R k = S.R k := by
    intro k hk hn132
    have hh := hframe k hk hn132
    have hn110 : k ≠ 110 := by intro he; subst k; norm_num at hk
    by_cases hn129 : k = 129
    · subst k; exact ⟨hh.1,by simp [H,h129]⟩
    · simpa [H,G,S₀,hn110,hn129] using hh
  refine ⟨v₃,H,(4*offsets.length+4)+(m₁+(m₂+(2*offsets.length+2))),hu₃.trans (hu₂.trans (hu₁.trans hu₀)),
    by dsimp only [reusablePackedCellBatchPublishCost]; dsimp only [w] at hm₂; omega,
    (Exec.seq he₀' (Exec.seq he₁ (Exec.seq he₂ he₃))).cast (by rw [h129G]) rfl,?_,?_,?_,hprojH,hframeH,?_,hvalid,hleftAll⟩
  · simpa [H,G] using h93
  · simpa [H,G] using h140F
  · simpa [H,G,S₀] using houtput
  · simpa [H,G] using hacc

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
