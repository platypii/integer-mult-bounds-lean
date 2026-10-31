module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareReplicaPublicationPages
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoutedGatheredPublication
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! Place the shared publication factory in the existing gather bank. Its exact
two-write endpoint makes the physical caller independent of bank case splits. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A span L : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def prepareGatheredPublicationPages (plan : ReplicaInteriorPlacement T) : Pr P T Q A U :=
  embProg (fun i : Fin 117 => plan.gather (Fin.castLE (by decide) i)) Empty.elim
    (prepareReplicaPublicationPages (P := Empty))

theorem prepareGatheredPublicationPages_exec_within (plan : ReplicaInteriorPlacement T) (V w : ℕ)
    (windows : PublicationWindows span L) (hw1 : 1 ≤ w)
    (hwV : w < 2^V) (hspanV : span < 2^V) (hvolume : span*w < 2^V)
    (v : HS T Q A U) (S : Stacks T A) (suffix : List (Fin (A+4)))
    (hV : (S.R (plan.gather 115)).length = V) (hw : (S.R (plan.gather 94)).length = w)
    (hL : (S.R (plan.gather 102)).length = L)
    (hsrc : S.R (plan.gather 109) = windows.origins.flatMap (binSyms V)++suffix)
    (hcount : S.R (plan.gather 116) = List.replicate windows.origins.length tick)
    (hblank : ∀ k : Fin 126, k.val < 19 → S.R (plan.gather k) = [])
    (hfresh : ∀ k ∈ [(88 : Fin 126),89,90,91,92,103,104,105,106,107], S.R (plan.gather k) = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ prepareReplicaPublicationPagesCost V span L w windows.origins.length ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        mnProgPush (prepareReplicaPublicationPages (P := Empty) (Q := Q) (A := A) (U := U))*
          prepareReplicaPublicationPagesCost V span L w windows.origins.length)
        depth (prepareGatheredPublicationPages plan) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R (plan.gather 103)
          (List.replicate (L*w) tick)) (plan.gather 92) (gatherControls A (windows.gaps w)))}) := by
  let e := fun i : Fin 117 => plan.gather (Fin.castLE (by decide) i)
  have he : Function.Injective e := plan.gather_injective.comp (Fin.castLE_injective (by decide))
  obtain ⟨vi,n,hu,hn,hei⟩ := prepareReplicaPublicationPages_exec_within V w windows hw1 hwV hspanV hvolume
    (embDn e v) (embStk e S) suffix hV hw hL hsrc hcount
    (by intro k hk; exact hblank (Fin.castLE (by decide) k) hk)
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hfresh _ (by simp)) depth
  obtain ⟨v',hv',hu',hei'⟩ := exec_emb_ovr_within_stock e he (body' := body)
    (fun p : Empty => nomatch p) hei v rfl S rfl
  have hbank : embOvr e (replicaPublicationPagesBank (embStk e S) windows w).get S =
      {S with R := (Function.update (Function.update S.R (plan.gather 103)
        (List.replicate (L*w) tick)) (plan.gather 92) (gatherControls A (windows.gaps w)))} :=
    embOvr_updateR_updateR he S 103 92 _ _
  rw [hbank] at hei'
  exact ⟨v',n,hu'.trans hu,hn,hei'⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
