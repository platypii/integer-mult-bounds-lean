module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedRecoveryCouplingRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingPlacement
public import IntegerMultBounds.MathlibTM2.Host.EmbedStockTrace
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! Place the cached recovery worker in the retained numerical bank. The
embedding preserves its complete time bill, storage bound and reusable cache. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def placedCachedRecoveryCouplingRow {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  embProg placement.bank Empty.elim (cachedLocalFeedCouplingInterval hQ)

def placedCachedRecoveryCouplingState {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (S : Stacks T A)
    (rhsTail output : List (Fin (A+4))) : Stacks T A :=
  {S with R := (Function.update (Function.update S.R (placement.bank 93) rhsTail)
    (placement.bank 110) (output++S.R (placement.bank 110)))}

theorem placedCachedRecoveryCouplingRow_exec_within (H : ReplicaHaloProblem s)
    {plan : ReplicaInteriorPlacement T} (placement : ReplicaCouplingPlacement plan)
    (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hsep : H.span+H.band ≤ s)
    (C B : ZMod s → GaussianInt) (hC : ∀ j, Fits H.wordWidth (C j))
    (tail rhsTail raw pageTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (cache : CachedRecoveryCouplingReady H raw pageTail (embStk placement.bank S))
    (hsource : S.R (placement.bank 132) = cstream A H.wordWidth (packedInterval H.origin H.span C)++tail)
    (hrhs : S.R (placement.bank 93) = cstream A H.wordWidth (packedInterval H.origin H.span B)++rhsTail) :
    let output := cstream A H.wordWidth (packedInterval H.origin H.span
      (guardedCouplingRowField (2^15*H.p) H.precision H.t H.u H.band
        H.origin (H.origin+H.span) true C B))
    let F := placedCachedRecoveryCouplingState placement S rhsTail output
    ∃ vf m, vf.user = v.user ∧ m ≤ cachedRecoveryCouplingRowCost H ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          cachedRecoveryCouplingWorkspace (A := A) (U := U) H hQ)
        depth (placedCachedRecoveryCouplingRow placement hQ) (mk v S) m (mk vf F)) ∧
      CachedRecoveryCouplingReady H (output++raw) pageTail (embStk placement.bank F) := by
  dsimp only
  let J := embStk placement.bank S
  let output := cstream A H.wordWidth (packedInterval H.origin H.span
    (guardedCouplingRowField (2^15*H.p) H.precision H.t H.u H.band
      H.origin (H.origin+H.span) true C B))
  obtain ⟨vi,m,hu,hm,he,hcache⟩ := cachedRecoveryCouplingRow_exec_within
    (body := fun p : Empty => nomatch p) H hQ hA hsep C B hC tail rhsTail raw pageTail
    (embDn placement.bank v) J cache hsource hrhs
  obtain ⟨vf,_,hu',hex⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    placement.bank_injective (fun p : Empty => nomatch p) (he 0).toExec v rfl S rfl
  have ht : embOvr placement.bank (cachedRecoveryCouplingState J rhsTail output).get S =
      placedCachedRecoveryCouplingState placement S rhsTail output := by
    unfold cachedRecoveryCouplingState
    rw [embOvr_updateR_updateR placement.bank_injective]
    rfl
  refine ⟨vf,m,hu'.trans hu,hm,?_,?_⟩
  · intro depth
    have hw := exec_emb_within_stock_of_exec (ι := Empty.elim) (body' := body)
      placement.bank_injective (fun p : Empty => nomatch p) (he depth) v rfl S rfl hex
    exact hw.cast rfl (congrArg (mk vf) ht)
  · rw [← ht,embStk_ovr placement.bank_injective]
    exact hcache

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
