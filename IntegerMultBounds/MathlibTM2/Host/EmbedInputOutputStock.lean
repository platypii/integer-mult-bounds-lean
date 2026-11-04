module

public import IntegerMultBounds.MathlibTM2.Host.EmbedStock

/-! Place a restoring consumer over arbitrary spectator storage. Its input
port returns to the baseline while the output port receives the computed word. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T T' Q A : ℕ} {P P' U : Type}

theorem exec_emb_input_output_within (e : Fin T → Fin T') (he : Function.Injective e)
    {ι : P → P'} {body : P → Pr P T Q A U} {body' : P' → Pr P' T' Q A U}
    (hbody : ∀ f, body' (ι f) = embProg e ι (body f))
    (src dst : Fin T) (xs ys : List (Fin (A+4))) (w : HS T' Q A U) (B : Stacks T' A)
    {p : Pr P T Q A U} {v' : HS T Q A U} {n depth budget : ℕ}
    (hex : ExecWithin body (fun d z => mnSize z+d ≤
        mnSize (mk (embDn e w) {embStk e B with R := Function.update (embStk e B).R src xs})+depth+budget)
      depth p (mk (embDn e w) {embStk e B with R := Function.update (embStk e B).R src xs}) n
      (mk v' {embStk e B with R := Function.update (embStk e B).R dst ys})) :
    ∃ w', w'.user = v'.user ∧
      ExecWithin body' (fun d z => mnSize z+d ≤
        mnSize (mk w {B with R := Function.update B.R (e src) xs})+depth+budget)
        depth (embProg e ι p) (mk w {B with R := Function.update B.R (e src) xs}) n
        (mk w' {B with R := Function.update B.R (e dst) ys}) := by
  let F : Stacks T' A := {B with R := Function.update B.R (e src) xs}
  obtain ⟨w',hdn,hu,ht⟩ := exec_emb_ovr_within_stock e he hbody hex w rfl F (embStk_updateR he B src xs)
  have hrestore : embOvr e (embStk e B).get F = B := by
    have hbase : embStk e B = {embStk e F with R := Function.update (embStk e F).R src (B.R (e src))} := by
      simp only [F,embStk_updateR he,Function.update_idem]
      change embStk e B = {embStk e B with R := Function.update (embStk e B).R src ((embStk e B).R src)}
      rw [Function.update_eq_self]
    rw [hbase,embOvr_updR he,embOvr_stk]
    simp only [F,Function.update_idem,Function.update_eq_self]
  rw [embOvr_updR he,hrestore] at ht
  exact ⟨w',hu,ht⟩

end IntegerMultBounds.MathlibTM2.Host
