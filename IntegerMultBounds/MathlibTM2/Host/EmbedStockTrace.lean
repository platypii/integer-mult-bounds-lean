module

public import IntegerMultBounds.MathlibTM2.Host.EmbedStock
public import IntegerMultBounds.MathlibTM2.StackExecutionUnique

/-! Attach a local storage bound to an existing placed trace, preserving its endpoint. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T T' Q A : ℕ} {P P' U : Type} {e : Fin T → Fin T'} {ι : P → P'}
  {body : P → Pr P T Q A U} {body' : P' → Pr P' T' Q A U}

theorem exec_emb_within_stock_of_exec (he : Function.Injective e)
    (hbody : ∀ f, body' (ι f) = embProg e ι (body f))
    {p : Pr P T Q A U} {v v' : HS T Q A U} {S F : Stacks T A}
    {steps depth budget : ℕ}
    (hex : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+budget)
      depth p (mk v S) steps (mk v' F))
    (w : HS T' Q A U) (hw : embDn e w = v) (B : Stacks T' A) (hB : embStk e B = S)
    {z : Store (HΓ (T := T') A) (HS T' Q A U)}
    (htrace : Exec body' (embProg e ι p) (mk w B) steps z) :
    ExecWithin body' (fun d z => mnSize z+d ≤ mnSize (mk w B)+depth+budget)
      depth (embProg e ι p) (mk w B) steps z := by
  obtain ⟨w',_,_,ht⟩ := exec_emb_ovr_within_stock e he hbody hex w hw B hB
  obtain ⟨_,hz⟩ := ht.toExec.unique htrace
  rw [hz] at ht
  exact ht

end IntegerMultBounds.MathlibTM2.Host
