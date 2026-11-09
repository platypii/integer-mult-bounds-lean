module

public import IntegerMultBounds.MathlibTM2.Fast.ResampBScanGrowthStock
public import IntegerMultBounds.MathlibTM2.Host.BinArithStock

/-! Counted register scans share a reserve when their completed bodies do not grow storage. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U R : Type} [DecidableEq R] {body : P → Pr P T Q A U}
  {rg : R → Fin T} {ι : Fin 64 → Fin T}

theorem rsb_scanIf_loop_within (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) {ra rt : R}
    (hat : ra ≠ rt) (c : Fin (A + 4) → Bool) (p q : Pr P T Q A U) (l : List (Fin (A + 4)))
    (Ψ : ℕ → R → List (Fin (A + 4))) (bp : ℕ → ℕ) (reserve : ℕ)
    (hbody : ∀ j (hj : j < l.length) X Y, RsbRunsWithin (body := body) (rg := rg) (ι := ι) (if c l[j] then p else q)
      (rsbUpd2 (Ψ j) ra X rt Y) (rsbUpd2 (Ψ (j + 1)) ra X rt Y) (bp j) reserve)
    (hstock : ∀ j < l.length, ∀ X Y (v v' : HS T Q A U) S F,
      RsbHolds rg S (rsbUpd2 (Ψ j) ra X rt Y) →
      RsbHolds rg F (rsbUpd2 (Ψ (j+1)) ra X rt Y) → RsbFr rg S F →
      mnSize (mk v' F) ≤ mnSize (mk v S)) :
    ∀ n j, j + n = l.length → ∀ v S, RsbClean ι S →
      RsbHolds rg S (rsbUpd2 (Ψ j) ra (l.drop j) rt (l.take j).reverse) →
      v.flag = (l.drop j).head?.isSome →
      ∃ v' S' m, v'.user = v.user ∧ m ≤ ∑ i ∈ Finset.range n, (bp (j + i) + 4) + 1 ∧
        (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+reserve)
          depth (.loop (·.flag) (.seq (.act (popPush (rg ra) (rg rt)))
          (.seq (.cond (fun v => c (v.sym.getD blank)) p q) (.act (peekR (rg ra))))))
          (mk v S) m (mk v' S')) ∧
        RsbHolds rg S' (rsbUpd2 (Ψ l.length) ra [] rt l.reverse) ∧ RsbFr rg S S' ∧ mnSize (mk v' S') ≤ mnSize (mk v S) := by
  have hs : ∀ j < l.length, ∀ X Y (v v' : HS T Q A U) S F,
      RsbHolds rg S (rsbUpd2 (Ψ j) ra X rt Y) →
      RsbHolds rg F (rsbUpd2 (Ψ (j+1)) ra X rt Y) → RsbFr rg S F →
      mnSize (mk v' F) ≤ mnSize (mk v S)+0 := by
    simpa only [Nat.add_zero] using hstock
  simpa only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] using
    rsb_scanIf_loop_within_growth hrg hdisj hat c p q l Ψ bp reserve 0 hbody hs

theorem rsb_scanIf_runs_within (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    {ra rt : R} (hat : ra ≠ rt) (c : Fin (A+4) → Bool) (p q : Pr P T Q A U)
    (l : List (Fin (A+4))) (Ψ : ℕ → R → List (Fin (A+4))) (bp : ℕ → ℕ) (reserve : ℕ)
    (hbody : ∀ j (hj : j < l.length) X Y,
      RsbRunsWithin (body := body) (rg := rg) (ι := ι) (if c l[j] then p else q)
        (rsbUpd2 (Ψ j) ra X rt Y) (rsbUpd2 (Ψ (j+1)) ra X rt Y) (bp j) reserve)
    (hstock : ∀ j < l.length, ∀ X Y (v v' : HS T Q A U) S F,
      RsbHolds rg S (rsbUpd2 (Ψ j) ra X rt Y) →
      RsbHolds rg F (rsbUpd2 (Ψ (j+1)) ra X rt Y) → RsbFr rg S F →
      mnSize (mk v' F) ≤ mnSize (mk v S)) :
    RsbRunsWithin (body := body) (rg := rg) (ι := ι)
      (rsbScanIf (rg ra) (rg rt) c p q) (rsbUpd2 (Ψ 0) ra l rt [])
      (rsbUpd2 (Ψ l.length) ra l rt [])
      (∑ i ∈ Finset.range l.length, (bp i+4)+2*l.length+4) reserve := by
  have hs : ∀ j < l.length, ∀ X Y (v v' : HS T Q A U) S F,
      RsbHolds rg S (rsbUpd2 (Ψ j) ra X rt Y) →
      RsbHolds rg F (rsbUpd2 (Ψ (j+1)) ra X rt Y) → RsbFr rg S F →
      mnSize (mk v' F) ≤ mnSize (mk v S)+0 := by
    simpa only [Nat.add_zero] using hstock
  simpa only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] using
    rsb_scanIf_runs_within_growth hrg hdisj hat c p q l Ψ bp reserve 0 hbody hs

theorem rsb_rep_runs_within (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    {ra rt : R} (hat : ra ≠ rt) (p : Pr P T Q A U) (l : List (Fin (A+4)))
    (Ψ : ℕ → R → List (Fin (A+4))) (time reserve : ℕ)
    (hbody : ∀ j < l.length, ∀ X Y,
      RsbRunsWithin (body := body) (rg := rg) (ι := ι) p
        (rsbUpd2 (Ψ j) ra X rt Y) (rsbUpd2 (Ψ (j+1)) ra X rt Y) time reserve)
    (hstock : ∀ j < l.length, ∀ X Y (v v' : HS T Q A U) S F,
      RsbHolds rg S (rsbUpd2 (Ψ j) ra X rt Y) →
      RsbHolds rg F (rsbUpd2 (Ψ (j+1)) ra X rt Y) → RsbFr rg S F →
      mnSize (mk v' F) ≤ mnSize (mk v S)) :
    RsbRunsWithin (body := body) (rg := rg) (ι := ι)
      (rsbRep (rg ra) (rg rt) p) (rsbUpd2 (Ψ 0) ra l rt [])
      (rsbUpd2 (Ψ l.length) ra l rt []) (l.length*(time+6)+4) reserve := by
  have hs : ∀ j < l.length, ∀ X Y (v v' : HS T Q A U) S F,
      RsbHolds rg S (rsbUpd2 (Ψ j) ra X rt Y) →
      RsbHolds rg F (rsbUpd2 (Ψ (j+1)) ra X rt Y) → RsbFr rg S F →
      mnSize (mk v' F) ≤ mnSize (mk v S)+0 := by
    simpa only [Nat.add_zero] using hstock
  simpa only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] using
    rsb_rep_runs_within_growth hrg hdisj hat p l Ψ time reserve 0 hbody hs

theorem RsbRunsWithin.congr_pre {p : Pr P T Q A U}
    {ρ σ τ : R → List (Fin (A+4))} {time reserve : ℕ}
    (h : RsbRunsWithin (body := body) (rg := rg) (ι := ι) p ρ τ time reserve) (he : ρ = σ) :
    RsbRunsWithin (body := body) (rg := rg) (ι := ι) p σ τ time reserve := by
  subst σ
  exact h

end IntegerMultBounds.MathlibTM2.Fast
