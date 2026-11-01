module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedBankLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoopSharedStock
public import IntegerMultBounds.MathlibTM2.Host.EmbedStockTrace

/-! A closed worker bank shares its reserve through an external consuming counter. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T T' Q A : ℕ} {P U : Type} {body : P → Pr P T' Q A U}

theorem countedBankLoop_exec_within (e : Fin T → Fin T') (he : Function.Injective e)
    (count : Fin T') (hoff : ∀ i, e i ≠ count) (p : Pr Empty T Q A U) (N c reserve : ℕ)
    (Inv : ℕ → Stacks T A → Prop)
    (hstep : ∀ r < N, ∀ (v : HS T Q A U) S, Inv r S →
      ∃ v' F n, v'.user = v.user ∧ n ≤ c ∧
        (∀ depth, ExecWithin (fun z : Empty => nomatch z)
          (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+reserve)
          depth p (mk v S) n (mk v' F)) ∧
        Inv (r+1) F ∧ mnSize (mk v' F) ≤ mnSize (mk v S))
    (v : HS T' Q A U) (S : Stacks T' A) (hcount : (S.R count).length = N)
    (hinitial : Inv 0 (embStk e S)) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ N*(c+3)+2 ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+reserve)
        depth (countedLoop count (embProg e Empty.elim p)) (mk v S) n (mk v' F)) ∧
      F.R count = [] ∧ Inv N (embStk e F) := by
  have hstable : ∀ r F xs, Inv r (embStk e F) →
      Inv r (embStk e {F with R := Function.update F.R count xs}) := by
    intro r F xs hI
    rw [embStk_updateR_off F count xs hoff]
    exact hI
  have hplaced : ∀ r < N, ∀ (vi : HS T' Q A U) F, Inv r (embStk e F) →
      ∃ vf G n, vf.user = vi.user ∧ n ≤ c ∧
        (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk vi F)+depth+reserve)
          depth (embProg e Empty.elim p) (mk vi F) n (mk vf G)) ∧
        G.R count = F.R count ∧ Inv (r+1) (embStk e G) ∧
        mnSize (mk vf G) ≤ mnSize (mk vi F) := by
    intro r hr vi F hI
    obtain ⟨w,G,n,hu,hn,hex,hG,hstock⟩ := hstep r hr (embDn e vi) (embStk e F) hI
    obtain ⟨vf,hv,hu',ht⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
      he (fun z => nomatch z) (hex 0).toExec vi rfl F rfl
    refine ⟨vf,embOvr e G.get F,n,hu'.trans hu,hn,?_,(embOvr_off G.get F hoff).2,?_,?_⟩
    · intro depth
      exact exec_emb_within_stock_of_exec he (fun z => nomatch z) (hex depth) vi rfl F rfl ht
    · rw [embStk_ovr he]; exact hG
    · change mnSize (mk vi (embOvr e G.get F)) ≤ mnSize (mk vi F)
      simpa only [Nat.add_zero] using embOvr_stock_le e he w vi G F 0
        (by simpa only [Nat.add_zero] using hstock)
  obtain ⟨v',F,n,hu,hn,ht,hc,hI⟩ := countedLoop_exec_costs_within count (embProg e Empty.elim p)
    N (fun _ => c) (fun r F => Inv r (embStk e F)) reserve hstable hplaced v S hcount hinitial
  exact ⟨v',F,n,hu,by simpa using hn,ht,hc,hI⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
