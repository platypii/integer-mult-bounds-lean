module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellEmptyPackedHaloGroup

/-! Test the generated count once, execute a nonempty numerical class or release
an empty class, and return the same packed-output and borrowed-source contract. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

noncomputable def conditionalPackedHaloPublish (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 168 Q A U :=
  .seq (.act (peekR 116)) (.cond (·.flag) (reusablePackedCellBatchPublish hR hQ) emptyPackedHaloGroup)

theorem conditionalPackedHaloPublish_sized_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l L s t p u target rhsExp origin N V : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hL : 0 < L) (hLs : L ≤ s) (hpad : L+L ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (offsets : List ℕ) (hdis : offsets.Pairwise (fun i j => i+L ≤ j))
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
      m ≤ (if offsets = [] then
        2*((2^15*p)+(executionStagePrecision p l target rhsExp+1)+q+l+s+t+u+PhaseCellBand.width p u+2*L)+21
        else reusablePackedCellBatchPublishCost p l target rhsExp V N L offsets.length s t u)+2 ∧
      Exec body (conditionalPackedHaloPublish hR hQ) (mk v S) m (mk v' F) ∧
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
  let v₀ : HS 168 Q A U := {v with flag := (S.R 116).head?.isSome}
  have hpeek : Exec body (.act (peekR 116)) (mk v S) 1 (mk v₀ S) := by
    simpa only [peekR_run,v₀] using Exec.act (body := body) (peekR 116) (mk v S)
  have hcount : S.R 116 = List.replicate offsets.length tick := by
    simpa [embStk,packedCellCoreReg,batchInputBank] using
      congrArg (fun B : Stacks 117 A => B.R 116) hbank
  by_cases hne : offsets ≠ []
  · obtain ⟨v₁,F,m,hu₁,hm,he,h93,h140F,houtput,hproj,hframe,hacc,hvalid,hleftAll⟩ :=
      reusablePackedCellBatchPublish_sized_exec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget
        hL hLs hpad C hC offsets hne hdis hhalo hfit hVeq hwV hcoords hunits tail outTail inp out
        v₀ S hbank E outputTail hE h129 h128 h130 h132 h140 hprotected h165 h166 hV h153 h155 h154
    have hflag : v₀.flag = true := by
      have hh : 0 < offsets.length := List.length_pos_iff.mpr hne
      cases hl : offsets.length with
      | zero => omega
      | succ n => simp [v₀,hcount,hl,List.replicate_succ]
    refine ⟨v₁,F,1+(m+1),hu₁,?_,Exec.seq hpeek (Exec.cond_true hflag he),
      h93,h140F,houtput,hproj,hframe,hacc,hvalid,hleftAll⟩
    simp only [ite_eq_right hne]; omega
  · have hz : offsets = [] := by simpa using hne
    subst offsets
    obtain ⟨v₁,F,hu₁,he,hproj,hframe⟩ := emptyPackedHaloGroup_exec (body := body)
      (2^15*p) (executionStagePrecision p l target rhsExp+1) (executionPrecision p l target rhsExp)
      l s t u (PhaseCellBand.width p u) L
      (cstream A (executionWidth p l target rhsExp) (packedInterval origin N C)++tail) outTail inp out v₀ S
      (by simpa [batchInputBank] using hbank)
    have hflag : v₀.flag = false := by simp [v₀,hcount]
    have h93 : F.R 93 = outTail := by
      simpa [embStk,packedCellCoreReg,releasedCellBank] using congrArg (fun B : Stacks 117 A => B.R 93) hproj
    refine ⟨v₁,F,1+((2*((2^15*p)+(executionStagePrecision p l target rhsExp+1)+
      executionPrecision p l target rhsExp+l+s+t+u+PhaseCellBand.width p u+2*L)+21)+1),
      hu₁,by simp; omega,Exec.seq hpeek (Exec.cond_false hflag he),h93,?_,?_,hproj,?_,?_,?_,?_⟩
    · rw [(hframe 140 (by decide)).2]; exact h140
    · rw [(hframe 132 (by decide)).2,h132]
      simp [packedCellGaps,windowGaps,scatterRows,scatterPrefix]
    · intro k hk _; exact hframe k hk
    · intro n; exact Fin.elim0 n
    · intro n; exact Fin.elim0 n

    · apply packedCell_left_eq
      · intro i
        have hF : F.L (packedCellCoreReg i) = [] := by
          simpa [embStk,releasedCellBank] using congrArg (fun B : Stacks 117 A => B.L i) hproj
        have hS : S.L (packedCellCoreReg i) = [] := by
          simpa [embStk,batchInputBank] using congrArg (fun B : Stacks 117 A => B.L i) hbank
        exact hF.trans hS.symm
      · intro k hk
        exact (hframe k hk).1

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
