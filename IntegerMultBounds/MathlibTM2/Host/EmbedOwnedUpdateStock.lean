module

public import IntegerMultBounds.MathlibTM2.Host.EmbedStock

/-! Place a restoring single-register kernel over an arbitrary background.
Its exact final update and stock allowance survive register renaming. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T T' Q A : ℕ} {P P' U : Type}

theorem exec_emb_owned_update_within (e : Fin T → Fin T') (he : Function.Injective e)
    {ι : P → P'} {body : P → Pr P T Q A U} {body' : P' → Pr P' T' Q A U}
    (hbody : ∀ f, body' (ι f) = embProg e ι (body f))
    (i : Fin T) (ys : List (Fin (A+4))) (w : HS T' Q A U) (B : Stacks T' A)
    {p : Pr P T Q A U} {v' : HS T Q A U} {n depth budget : ℕ}
    (hex : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk (embDn e w) (embStk e B))+depth+budget)
      depth p (mk (embDn e w) (embStk e B)) n
      (mk v' {embStk e B with R := Function.update (embStk e B).R i ys})) :
    ∃ w', w'.user = v'.user ∧
      ExecWithin body' (fun d z => mnSize z+d ≤ mnSize (mk w B)+depth+budget)
        depth (embProg e ι p) (mk w B) n (mk w' {B with R := Function.update B.R (e i) ys}) := by
  obtain ⟨w',hdn,hu,ht⟩ := exec_emb_ovr_within_stock e he hbody hex w rfl B rfl
  rw [embOvr_updR he,embOvr_stk] at ht
  exact ⟨w',hu,ht⟩

end IntegerMultBounds.MathlibTM2.Host
