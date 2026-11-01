module

public import IntegerMultBounds.MathlibTM2.Fast.BandLineNativeStock
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Register-file execution contracts with an additive local workspace bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U R : Type} {body : P → Pr P T Q A U}
  {rg : R → Fin T} {ι : Fin 64 → Fin T}

def RsbRunsWithin (p : Pr P T Q A U) (ρ ρ' : R → List (Fin (A+4))) (time stock : ℕ) : Prop :=
  ∀ v S, RsbClean ι S → RsbHolds rg S ρ → ∃ v' F n,
    v'.user = v.user ∧ n ≤ time ∧ RsbHolds rg F ρ' ∧ RsbFr rg S F ∧
    ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+stock)
      depth p (mk v S) n (mk v' F)

theorem RsbRuns.within_native {p : Pr P T Q A U} {ρ ρ' : R → List (Fin (A+4))}
    {time c : ℕ} (h : RsbRuns body rg ι p ρ ρ' time) (hp : mnNativePushBound c p) :
    RsbRunsWithin (body := body) (rg := rg) (ι := ι) p ρ ρ' time (c*time) :=
  fun v S hc hS => h.exec_within_native hp v S hc hS

theorem RsbRunsWithin.seq (hdisj : ∀ r j, rg r ≠ ι j)
    {p q : Pr P T Q A U} {ρ σ τ : R → List (Fin (A+4))} {m n a b : ℕ}
    (hp : RsbRunsWithin (body := body) (rg := rg) (ι := ι) p ρ σ m a)
    (hq : RsbRunsWithin (body := body) (rg := rg) (ι := ι) q σ τ n b) :
    RsbRunsWithin (body := body) (rg := rg) (ι := ι) (.seq p q) ρ τ (m+n) (a+b) := by
  intro v S hc hS
  obtain ⟨v₁,F,m',hu₁,hm,hh₁,hf₁,he₁⟩ := hp v S hc hS
  obtain ⟨v₂,G,n',hu₂,hn,hh₂,hf₂,he₂⟩ := hq v₁ F (hc.of_fr hdisj hf₁) hh₁
  exact ⟨v₂,G,m'+n',hu₂.trans hu₁,Nat.add_le_add hm hn,hh₂,hf₁.trans hf₂,
    fun depth => mn_seq_within_add (he₁ depth) (he₂ depth)⟩

theorem RsbRunsWithin.congr {p : Pr P T Q A U} {ρ σ τ : R → List (Fin (A+4))} {m a : ℕ}
    (h : RsbRunsWithin (body := body) (rg := rg) (ι := ι) p ρ σ m a) (he : σ = τ) :
    RsbRunsWithin (body := body) (rg := rg) (ι := ι) p ρ τ m a := by
  subst τ
  exact h

theorem RsbRunsWithin.mono {p : Pr P T Q A U} {ρ σ : R → List (Fin (A+4))} {m n a b : ℕ}
    (h : RsbRunsWithin (body := body) (rg := rg) (ι := ι) p ρ σ m a)
    (ht : m ≤ n) (hs : a ≤ b) :
    RsbRunsWithin (body := body) (rg := rg) (ι := ι) p ρ σ n b := by
  intro v S hc hS
  obtain ⟨v',F,k,hu,hk,hh,hf,he⟩ := h v S hc hS
  exact ⟨v',F,k,hu,hk.trans ht,hh,hf,fun depth =>
    (he depth).mono (by intro d z hz; omega)⟩

end IntegerMultBounds.MathlibTM2.Fast
