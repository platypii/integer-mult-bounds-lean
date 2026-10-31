module

public import IntegerMultBounds.MathlibTM2.Fast.RingProdRegs
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Resource-aware register-file contracts compose the same actual stages as
RpRuns. Native format work uses its linear traffic budget; arithmetic supplies
its separately proved workspace certificate. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {rg : RpReg → Fin T} {ι : Fin 91 → Fin T}

def RpRunsWithin (body : P → Pr P T Q A U) (rg : RpReg → Fin T) (ι : Fin 91 → Fin T)
    (p : Pr P T Q A U) (ρ ρ' : RpReg → List (Fin (A+4))) (time stock : ℕ) : Prop :=
  ∀ (v : HS T Q A U) (S : Stacks T A), RpClean ι S → RpHolds rg S ρ →
    ∃ v' S' n, v'.user = v.user ∧ n ≤ time ∧ RpHolds rg S' ρ' ∧ RpFr rg S S' ∧
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+stock)
        depth p (mk v S) n (mk v' S')

theorem RpRuns.within_native {p : Pr P T Q A U} {ρ ρ' : RpReg → List (Fin (A+4))} {time c : ℕ}
    (h : RpRuns body rg ι p ρ ρ' time) (hp : mnNativePushBound c p) :
    RpRunsWithin body rg ι p ρ ρ' time (c*time) := by
  intro v S hc hS
  obtain ⟨v',S',n,hu,hn,he,hS',hf⟩ := h v S hc hS
  refine ⟨v',S',n,hu,hn,hS',hf,?_⟩
  intro depth
  exact mn_native_exec_within he c hp depth _
    (Nat.add_le_add_left (Nat.mul_le_mul_left c hn) _)

theorem RpRunsWithin.seq (h : RpLayout rg ι) {p q : Pr P T Q A U}
    {ρ₁ ρ₂ ρ₃ : RpReg → List (Fin (A+4))} {t₁ t₂ b₁ b₂ : ℕ}
    (hp : RpRunsWithin body rg ι p ρ₁ ρ₂ t₁ b₁)
    (hq : RpRunsWithin body rg ι q ρ₂ ρ₃ t₂ b₂) :
    RpRunsWithin body rg ι (.seq p q) ρ₁ ρ₃ (t₁+t₂) (b₁+b₂) := by
  intro v S hc hS
  obtain ⟨v₁,S₁,n₁,hu₁,hn₁,hS₁,hf₁,ht₁⟩ := hp v S hc hS
  obtain ⟨v₂,S₂,n₂,hu₂,hn₂,hS₂,hf₂,ht₂⟩ := hq v₁ S₁ (hc.of_fr h hf₁) hS₁
  exact ⟨v₂,S₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,hS₂,hf₁.trans hf₂,
    fun depth => mn_seq_within_add (ht₁ depth) (ht₂ depth)⟩

end IntegerMultBounds.MathlibTM2.Fast
