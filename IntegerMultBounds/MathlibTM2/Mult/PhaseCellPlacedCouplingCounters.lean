module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingReadinessStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCouplingCounters
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock

/-! Generate retained scalar counters through any injective native-bank placement.
Everything outside that bank survives, including shared coefficient pages. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def placedCouplingCounters (e : Fin 117 → Fin T) : Pr P T Q A U :=
  embProg e Empty.elim (couplingReadiness (P₀ := Empty))

def replicaCouplingCountersCost (q w band : ℕ) := prepareCost q w+6*q+4*band+10

theorem placedCouplingCounters_exec_within (e : Fin 117 → Fin T) (he : Function.Injective e)
    {precision q w s t u band a b : ℕ} (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (raw : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hready : CouplingReady precision q w s t u band a b raw (embStk e S)) (depth : ℕ) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ replicaCouplingCountersCost q w band ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*replicaCouplingCountersCost q w band) depth
        (placedCouplingCounters e) (mk v S) n (mk v' F) ∧
      RetainedCouplingReady precision q w s t u band a b raw (embStk e F) ∧
      embStk e F = {embStk e S with R := counterR q w (embStk e S).R} ∧
      F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ k, (∀ i, e i ≠ k) → F.R k = S.R k) := by
  obtain ⟨vi,n,hu,hn,hex,hretained⟩ := retainedCouplingCounters_exec (body := fun p : Empty => nomatch p)
    q w hw5 hqw raw (embDn e v) (embStk e S) hready
  have hwithin := mn_native_exec_within hex 3 couplingReadiness_native depth _
    (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hn) _)
  obtain ⟨v',_,hu',he'⟩ := exec_emb_ovr_within_stock e he (body' := body) (ι := Empty.elim)
    (fun p : Empty => nomatch p) hwithin v rfl S rfl
  let F := embOvr e {embStk e S with R := counterR q w (embStk e S).R}.get S
  have hview : embStk e F = {embStk e S with R := counterR q w (embStk e S).R} := embStk_ovr he _ S
  refine ⟨v',F,n,hu'.trans hu,hn,he',?_,hview,embOvr_right_left S _,rfl,rfl,?_⟩
  · rw [hview]
    exact hretained
  · intro k hk
    exact (embOvr_off _ S hk).2

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
