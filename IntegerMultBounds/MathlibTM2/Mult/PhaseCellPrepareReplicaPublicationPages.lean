module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedWindowPublicationControls
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.Host.ClosedProgramStock

/-! Generate the window-volume and scatter-control pages once from retained
headers and binary origins. All other state, including origin suffixes, survives. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A s L : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def prepareReplicaPublicationPages : Pr P 117 Q A U :=
  .seq (unaryProduct 102 94 103 104 105) preparedWindowPublicationControls

def prepareReplicaPublicationPagesCost (V s L w B : ℕ) :=
  (L*(4*w+9)+4)+(preparedOriginAdvanceCost V s w B+37*s*w+2*B+29)

def replicaPublicationPagesBank (S : Stacks 117 A) (windows : PublicationWindows s L) (w : ℕ) : Stacks 117 A :=
  {S with R := (Function.update (Function.update S.R 103 (List.replicate (L*w) tick))
    92 (gatherControls A (windows.gaps w)))}

theorem prepareReplicaPublicationPages_exec (V w : ℕ)
    (windows : PublicationWindows s L) (hw1 : 1 ≤ w)
    (hwV : w < 2^V) (hsV : s < 2^V) (hvolume : s*w < 2^V)
    (v : HS 117 Q A U) (S : Stacks 117 A) (suffix : List (Fin (A+4)))
    (hV : (S.R 115).length = V) (hw : (S.R 94).length = w) (hL : (S.R 102).length = L)
    (hsrc : S.R 109 = windows.origins.flatMap (binSyms V)++suffix)
    (hcount : S.R 116 = List.replicate windows.origins.length tick)
    (hblank : ∀ k : Fin 117, k.val < 19 → S.R k = [])
    (hfresh : ∀ k ∈ [(88 : Fin 117),89,90,91,92,103,104,105,106,107], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ prepareReplicaPublicationPagesCost V s L w windows.origins.length ∧
      Exec body prepareReplicaPublicationPages (mk v S) n (mk v' (replicaPublicationPagesBank S windows w)) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := 102) (b := 94) (dst := 103) (t₁ := 104) (t₂ := 105) (by decide)
    v S (hfresh _ (by simp)) (hfresh _ (by simp))
  let M : Stacks 117 A := {S with R := Function.update S.R 103 (List.replicate (L*w) tick)}
  have he₁' : Exec body (unaryProduct 102 94 103 104 105) (mk v S) n₁ (mk v₁ M) := by
    simpa only [hL,hw,hfresh 103 (by simp),List.append_nil] using he₁
  have hoff (k : Fin 117) (hk : k ≠ 103) : M.R k = S.R k := by simp [M,hk]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := preparedWindowPublicationControls_exec (body := body)
    V w windows hw1 hwV hsV hvolume v₁ M suffix
    (by rw [hoff 115 (by decide)]; exact hV)
    (by rw [hoff 94 (by decide)]; exact hw)
    (by rw [hoff 109 (by decide)]; exact hsrc)
    (by rw [hoff 116 (by decide)]; exact hcount)
    (by simp [M])
    (by intro k hk; rw [hoff k (by intro he; subst k; norm_num at hk)]; exact hblank k hk)
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals rw [hoff _ (by decide)]; exact hfresh _ (by simp))
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,?_,?_⟩
  · dsimp only [prepareReplicaPublicationPagesCost]
    rw [hL,hw] at hn₁
    exact Nat.add_le_add hn₁ hn₂
  · simpa [prepareReplicaPublicationPages,replicaPublicationPagesBank,M,hfresh 92 (by simp)] using Exec.seq he₁' he₂

/-- The table compiler is charged only in this shared setup allowance. -/
theorem prepareReplicaPublicationPages_exec_within (V w : ℕ)
    (windows : PublicationWindows s L) (hw1 : 1 ≤ w)
    (hwV : w < 2^V) (hsV : s < 2^V) (hvolume : s*w < 2^V)
    (v : HS 117 Q A U) (S : Stacks 117 A) (suffix : List (Fin (A+4)))
    (hV : (S.R 115).length = V) (hw : (S.R 94).length = w) (hL : (S.R 102).length = L)
    (hsrc : S.R 109 = windows.origins.flatMap (binSyms V)++suffix)
    (hcount : S.R 116 = List.replicate windows.origins.length tick)
    (hblank : ∀ k : Fin 117, k.val < 19 → S.R k = [])
    (hfresh : ∀ k ∈ [(88 : Fin 117),89,90,91,92,103,104,105,106,107], S.R k = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ prepareReplicaPublicationPagesCost V s L w windows.origins.length ∧
      ExecWithin (fun p : Empty => nomatch p)
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          mnProgPush (prepareReplicaPublicationPages (P := Empty) (Q := Q) (A := A) (U := U))*
            prepareReplicaPublicationPagesCost V s L w windows.origins.length)
        depth prepareReplicaPublicationPages (mk v S) n (mk v' (replicaPublicationPagesBank S windows w)) := by
  obtain ⟨v',n,hu,hn,he⟩ := prepareReplicaPublicationPages_exec
    (body := fun p : Empty => nomatch p) V w windows hw1 hwV hsV hvolume v S suffix
    hV hw hL hsrc hcount hblank hfresh
  exact ⟨v',n,hu,hn,mn_native_exec_within he _ (WordCmd.empty_native _) depth _
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ hn) _)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
