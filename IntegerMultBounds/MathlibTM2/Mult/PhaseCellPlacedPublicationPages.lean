module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareReplicaPublicationPages
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock

/-! Place the existing publication-page factory over an arbitrary caller bank.
Only its control page and window-volume counter change. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A s L : ℕ} {P U : Type}

theorem placedPublicationPages_exec_within (body : P → Pr P T Q A U)
    (e : Fin 117 → Fin T) (he : Function.Injective e) (V w : ℕ)
    (windows : PublicationWindows s L) (hw1 : 1 ≤ w)
    (hwV : w < 2^V) (hsV : s < 2^V) (hvolume : s*w < 2^V)
    (v : HS T Q A U) (S : Stacks T A) (suffix : List (Fin (A+4)))
    (hV : (S.R (e 115)).length = V) (hw : (S.R (e 94)).length = w)
    (hL : (S.R (e 102)).length = L)
    (hsrc : S.R (e 109) = windows.origins.flatMap (binSyms V)++suffix)
    (hcount : S.R (e 116) = List.replicate windows.origins.length tick)
    (hblank : ∀ k : Fin 117, k.val < 19 → S.R (e k) = [])
    (hfresh : ∀ k ∈ [(88 : Fin 117),89,90,91,92,103,104,105,106,107], S.R (e k) = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ prepareReplicaPublicationPagesCost V s L w windows.origins.length ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        mnProgPush (prepareReplicaPublicationPages (P := Empty) (Q := Q) (A := A) (U := U))*
          prepareReplicaPublicationPagesCost V s L w windows.origins.length) depth
        (embProg e Empty.elim (prepareReplicaPublicationPages (P := Empty))) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R (e 103)
          (List.replicate (L*w) tick)) (e 92) (gatherControls A (windows.gaps w)))}) := by
  obtain ⟨vi,n,hu,hn,hei⟩ := prepareReplicaPublicationPages_exec_within V w windows hw1 hwV hsV hvolume
    (embDn e v) (embStk e S) suffix hV hw hL hsrc hcount hblank hfresh depth
  obtain ⟨v',hv',hu',hei'⟩ := exec_emb_ovr_within_stock e he (body' := body)
    (fun p : Empty => nomatch p) hei v rfl S rfl
  have hbank : embOvr e (replicaPublicationPagesBank (embStk e S) windows w).get S =
      {S with R := (Function.update (Function.update S.R (e 103)
        (List.replicate (L*w) tick)) (e 92) (gatherControls A (windows.gaps w)))} :=
    embOvr_updateR_updateR he S 103 92 _ _
  rw [hbank] at hei'
  exact ⟨v',n,hu'.trans hu,hn,hei'⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
