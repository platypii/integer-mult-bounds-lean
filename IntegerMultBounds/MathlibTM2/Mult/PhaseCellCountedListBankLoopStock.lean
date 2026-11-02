module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedListLoopStock
public import IntegerMultBounds.MathlibTM2.Host.EmbedStockTrace

/-! A closed fixed worker consumes a mathematical schedule under an external
counter. The counter needs no slot in the reusable worker bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T T' Q A : ℕ} {P U E : Type} {body : P → Pr P T' Q A U}

theorem countedListBankLoop_exec_within (e : Fin T → Fin T') (he : Function.Injective e)
    (count : Fin T') (hoff : ∀ i, e i ≠ count) (run : Pr Empty T Q A U)
    (rs : List E) (cost : E → ℕ) (Ready : List E → Stacks T A → Prop) (reserve : ℕ)
    (hstep : ∀ r ∈ rs, ∀ xs (v : HS T Q A U) S, Ready (r::xs) S →
      ∃ v' F n, v'.user = v.user ∧ n ≤ cost r ∧
        (∀ depth, ExecWithin (fun z : Empty => nomatch z)
          (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+reserve)
          depth run (Host.mk v S) n (Host.mk v' F)) ∧
        Ready xs F ∧ mnSize (Host.mk v' F) ≤ mnSize (Host.mk v S))
    (v : HS T' Q A U) (S : Stacks T' A) (hcount : (S.R count).length = rs.length)
    (hReady : Ready rs (embStk e S)) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ (rs.map (fun r => cost r+3)).sum+2 ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+reserve)
        depth (countedLoop count (embProg e Empty.elim run)) (Host.mk v S) n (Host.mk v' F)) ∧
      F.R count = [] ∧ Ready [] (embStk e F) := by
  have hstable : ∀ xs F word, Ready xs (embStk e F) →
      Ready xs (embStk e {F with R := Function.update F.R count word}) := by
    intro xs F word hI
    rw [embStk_updateR_off F count word hoff]
    exact hI
  have hplaced : ∀ r ∈ rs, ∀ xs (vi : HS T' Q A U) F, Ready (r::xs) (embStk e F) →
      ∃ vf G n, vf.user = vi.user ∧ n ≤ cost r ∧
        (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk vi F)+depth+reserve)
          depth (embProg e Empty.elim run) (Host.mk vi F) n (Host.mk vf G)) ∧
        G.R count = F.R count ∧ Ready xs (embStk e G) ∧
        mnSize (Host.mk vf G) ≤ mnSize (Host.mk vi F) := by
    intro r hr xs vi F hI
    obtain ⟨w,G,n,hu,hn,hex,hG,hs⟩ := hstep r hr xs (embDn e vi) (embStk e F) hI
    obtain ⟨vf,hv,hu',ht⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
      he (fun z => nomatch z) (hex 0).toExec vi rfl F rfl
    refine ⟨vf,embOvr e G.get F,n,hu'.trans hu,hn,?_,(embOvr_off G.get F hoff).2,?_,?_⟩
    · intro depth
      exact exec_emb_within_stock_of_exec he (fun z => nomatch z) (hex depth) vi rfl F rfl ht
    · rw [embStk_ovr he]; exact hG
    · change mnSize (Host.mk vi (embOvr e G.get F)) ≤ mnSize (Host.mk vi F)
      simpa only [Nat.add_zero] using embOvr_stock_le e he w vi G F 0
        (by simpa only [Nat.add_zero] using hs)
  exact countedListLoop_exec_within count (embProg e Empty.elim run) rs cost
    (fun xs F => Ready xs (embStk e F)) reserve hstable hplaced v S hcount hReady

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
