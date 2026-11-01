module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! Iterate a closed worker with a counter outside its placed bank. The worker
invariant never sees counter updates, and no worker frame proof is needed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
variable {T T' Q A : ℕ} {P U : Type} {body : P → Pr P T' Q A U}

theorem countedBankLoop_exec (e : Fin T → Fin T') (he : Function.Injective e)
    (count : Fin T') (hoff : ∀ i, e i ≠ count) (p : Pr Empty T Q A U) (N c : ℕ)
    (Inv : ℕ → Stacks T A → Prop)
    (hstep : ∀ r < N, ∀ (v : HS T Q A U) S, Inv r S →
      ∃ v' F n, v'.user = v.user ∧ n ≤ c ∧
        Exec (fun z : Empty => nomatch z) p (mk v S) n (mk v' F) ∧ Inv (r+1) F)
    (v : HS T' Q A U) (S : Stacks T' A) (hcount : (S.R count).length = N)
    (hinitial : Inv 0 (embStk e S)) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ N*(c+3)+2 ∧
      Exec body (countedLoop count (embProg e Empty.elim p)) (mk v S) n (mk v' F) ∧
      F.R count = [] ∧ Inv N (embStk e F) := by
  apply countedLoop_exec count (embProg e Empty.elim p) N c (fun r F => Inv r (embStk e F))
    ?_ ?_ v S hcount hinitial
  · intro r F xs hI
    rw [embStk_updateR_off F count xs hoff]
    exact hI
  · intro r hr vi F hI
    obtain ⟨vf,G,n,hu,hn,hex,hG⟩ := hstep r hr (embDn e vi) (embStk e F) hI
    obtain ⟨v',hv,hu',hex'⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
      he (fun z => nomatch z) hex vi rfl F rfl
    exact ⟨v',embOvr e G.get F,n,hu'.trans hu,hn,hex',
      (embOvr_off G.get F hoff).2,by rw [embStk_ovr he]; exact hG⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
