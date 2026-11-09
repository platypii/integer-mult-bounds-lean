module

public import IntegerMultBounds.MathlibTM2.Host.EmbedStock
public import IntegerMultBounds.MathlibTM2.Host.RightUpdates

/-! Finite right-bank effects lift through any injective tape layout with
spectators counted once, at arbitrary caller depth. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T T' Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- Lift any finite right-bank effect without expanding the surrounding bank. -/
theorem exec_emb_rightUpdates_within_stock (e : Fin T → Fin T') (he : Function.Injective e)
    (p : Pr P T Q A U) (v : HS T' Q A U) (S : Stacks T' A)
    (vi : HS T Q A U) (n depth work : ℕ) (writes : List (Fin T × List (Fin (A+4))))
    (hu : vi.user = v.user)
    (hex : ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk (embDn e v) (embStk e S))+depth+work)
      depth p (mk (embDn e v) (embStk e S)) n (mk vi (rightUpdates writes (embStk e S)))) :
    ∃ vf, vf.user = v.user ∧ ExecWithin (embTab e body)
      (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+work)
      depth (embProg e id p) (mk v S) n
      (mk vf (rightUpdates (writes.map (fun (i,xs) => (e i,xs))) S)) := by
  obtain ⟨vf,_,huser,ht⟩ := exec_emb_ovr_within_stock e (ι := id) (body' := embTab e body)
    he (fun _ => rfl) hex v rfl S rfl
  refine ⟨vf,huser.trans hu,ht.cast rfl ?_⟩
  apply congrArg (mk vf)
  rw [embOvr_rightUpdates he,embOvr_stk]

theorem exec_emb_twoPorts_within_stock (e : Fin T → Fin T') (he : Function.Injective e)
    (i j : Fin T) (p : Pr P T Q A U) (v : HS T' Q A U) (S : Stacks T' A)
    (vi : HS T Q A U) (n depth work : ℕ) (input output : List (Fin (A+4)))
    (hu : vi.user = v.user)
    (hex : ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk (embDn e v) (embStk e S))+depth+work)
      depth p (mk (embDn e v) (embStk e S)) n
      (mk vi {(embStk e S) with R := (Function.update
        (Function.update (embStk e S).R i input) j output)})) :
    ∃ vf, vf.user = v.user ∧ ExecWithin (embTab e body)
      (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+work)
      depth (embProg e id p) (mk v S) n
      (mk vf {S with R := Function.update (Function.update S.R (e i) input) (e j) output}) := by
  exact exec_emb_rightUpdates_within_stock e he p v S vi n depth work [(i,input),(j,output)] hu hex

end IntegerMultBounds.MathlibTM2.Host
