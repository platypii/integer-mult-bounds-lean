module

public import IntegerMultBounds.Machine.HoareWithin
public import IntegerMultBounds.Machine.LoopChain

/-! A while-chain shares one prefix predicate across real tests, body runs
and returns. Runtime budgets add without accumulating workspace allowances. -/
@[expose] public section
namespace IntegerMultBounds.Machine
variable {t q a : ℕ} {M : Program t q a} {H : TapePred t a}

namespace RunWithin

theorem while_iteration (test) {v : Tapes t a} {c : Config t q a} {k : ℕ}
    (h : RunWithin M H k (v.start M) c) (ht : test v.reads = true) (hh : step M c = none) :
    RunWithin (whileLoop M test) H (k+2) (v.start (whileLoop M test))
      (c.tapes.start (whileLoop M test)) := by
  have he := RunWithin.single (while_step_enter M test v ht) h.initial h.initial
  have hb := h.simulation (N := whileLoop M test) (G := H) (fun c => c.mapState (Fin.castAdd 1))
    (fun _ _ hs => while_step_body M test hs) (fun _ hs => hs)
  have hr := RunWithin.single (while_step_return M test hh) h.finish h.finish
  have hw := (he.trans hb).trans hr
  simpa only [show 1+k+1 = k+2 by omega] using hw

end RunWithin
namespace HoareWithin

theorem while_chain_run (M : Program t q a) (test) (X : ℕ → Tapes t a) (cost : ℕ → ℕ)
    (H : TapePred t a) (hzero : H (X 0)) (n : ℕ)
    (hbody : ∀ j < n, HoareWithin M (· = X j) (· = X (j+1)) (cost j) H)
    (htest : ∀ j < n, test (X j).reads = true) :
    ∃ k ≤ ∑ j ∈ Finset.range n, (cost j+2),
      RunWithin (whileLoop M test) H k ((X 0).start (whileLoop M test))
        ((X n).start (whileLoop M test)) := by
  induction n with
  | zero => exact ⟨0,by simp,RunWithin.refl hzero⟩
  | succ n ih =>
    obtain ⟨k,hk,hr⟩ := ih (fun j hj => hbody j (by omega)) (fun j hj => htest j (by omega))
    obtain ⟨m,hm,c,hc,hh,hpost⟩ := hbody n (by omega) (X n) rfl
    have hi := hc.while_iteration test (htest n (by omega)) hh
    rw [hpost] at hi
    refine ⟨k+(m+2),?_,hr.trans hi⟩
    rw [Finset.sum_range_succ]
    omega

theorem while_chain (M : Program t q a) (test) (X : ℕ → Tapes t a) (cost : ℕ → ℕ)
    (H : TapePred t a) (hzero : H (X 0)) (n : ℕ)
    (hbody : ∀ j < n, HoareWithin M (· = X j) (· = X (j+1)) (cost j) H)
    (htest : ∀ j < n, test (X j).reads = true) (hexit : test (X n).reads = false) :
    HoareWithin (whileLoop M test) (· = X 0) (· = X n)
      (∑ j ∈ Finset.range n, (cost j+2)) H := by
  rintro v rfl
  obtain ⟨k,hk,hr⟩ := while_chain_run M test X cost H hzero n hbody htest
  exact ⟨k,hk,_,hr,while_step_exit M test (X n) hexit,rfl⟩

end HoareWithin
end IntegerMultBounds.Machine
