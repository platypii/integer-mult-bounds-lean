module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryExchangeCall

/-! Structural schedules of actual binary-input interval exchanges. Every call
includes dimension conversion, header generation and complete metadata cleanup. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

variable {J : Type*} {t₀ T Q K n R B : ℕ} {str tmp : Fin T} {U F : Type}

noncomputable def binaryExchangeChain (calls : J → BinaryExchangeCall t₀ T Q n R B str tmp) :
    List J → Pr F T Q (prime + K) U
  | [] => .act .done
  | j :: js => .seq (calls j).program (binaryExchangeChain calls js)

noncomputable def binaryExchangeChainCost (calls : J → BinaryExchangeCall t₀ T Q n R B str tmp)
    (S : Stacks T (prime + K)) : List J → ℝ
  | [] => 1
  | j :: js => (calls j).cost S + binaryExchangeChainCost calls S js

theorem binaryExchangeChainCost_le (calls : J → BinaryExchangeCall t₀ T Q n R B str tmp)
    (S : Stacks T (prime + K)) (js : List J) (budget : ℝ)
    (hcost : ∀ j ∈ js, (calls j).cost S ≤ budget) :
    binaryExchangeChainCost calls S js ≤ js.length * budget + 1 := by
  induction js with
  | nil => simp [binaryExchangeChainCost]
  | cons j js ih =>
    have hc := hcost j (by simp)
    have ht := ih (fun k hk => hcost k (List.mem_cons_of_mem _ hk))
    simp only [binaryExchangeChainCost, List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith only [hc, ht]

theorem binaryExchangeChainCost_le_sum (calls : J → BinaryExchangeCall t₀ T Q n R B str tmp)
    (S : Stacks T (prime + K)) (js : List J) (price : J → ℝ) (a b : ℝ)
    (hcost : ∀ j ∈ js, (calls j).cost S ≤ a * price j + b) :
    binaryExchangeChainCost calls S js ≤ a * (js.map price).sum + js.length * b + 1 := by
  induction js with
  | nil => simp [binaryExchangeChainCost]
  | cons j js ih =>
    have hc := hcost j (by simp)
    have ht := ih (fun k hk => hcost k (List.mem_cons_of_mem _ hk))
    simp only [binaryExchangeChainCost, List.map_cons, List.sum_cons, List.length_cons,
      Nat.cast_add, Nat.cast_one]
    linarith only [hc, ht]

theorem binaryExchangeChainCost_updateStream (calls : J → BinaryExchangeCall t₀ T Q n R B str tmp)
    (S : Stacks T (prime + K)) (out : List (Fin (prime + K + 4))) (js : List J) :
    binaryExchangeChainCost calls { S with R := Function.update S.R str out } js =
      binaryExchangeChainCost calls S js := by
  induction js with
  | nil => rfl
  | cons j js ih => simp only [binaryExchangeChainCost, BinaryExchangeCall.cost_updateStream, ih]

/-- All schedule stages execute from binary coordinate tapes. The only premises
about later calls are their original tape invariants, never execution oracles. -/
theorem binaryExchangeChain_exec (body : F → Pr F T Q (prime + K) U)
    (calls : J → BinaryExchangeCall t₀ T Q n R B str tmp) (js : List J)
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (hready : ∀ j, (calls j).Ready S)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ n)
    (hlB : ∀ r ∈ l, r.length = B) (h8 : ∀ r ∈ l, ∀ s ∈ r, s.val < 8)
    (hsrc : S.R str = l.flatten) :
    ∃ (v' : HS T Q (prime + K) U) (m : ℕ), v'.user = v.user ∧
      (m : ℝ) ≤ binaryExchangeChainCost calls S js ∧
      Exec body (binaryExchangeChain calls js) (mk v S) m
        (mk v' { S with R := Function.update S.R str (exchangeChainData (R := R) (fun j => (calls j).spec) js l).flatten }) := by
  induction js generalizing v S l with
  | nil =>
    refine ⟨v, 1, rfl, by simp [binaryExchangeChainCost], ?_⟩
    have hbank : Function.update S.R str l.flatten = S.R := by
      rw [← hsrc]
      exact Function.update_eq_self _ _
    simpa only [binaryExchangeChain, exchangeChainData, hbank, Action.run] using
      (Exec.act (body := body) .done (mk v S))
  | cons j js ih =>
    obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := (calls j).exec body v S (hready j) l hl hlB h8 hsrc
    let l₁ := moveRecs ((calls j).spec.rank R) l
    let S₁ : Stacks T (prime + K) := { S with R := Function.update S.R str l₁.flatten }
    have hl₁ : l₁.length = R * 2 ^ n := length_moveRecs _ _
    have hmem : ∀ r ∈ l₁, r ∈ l := fun r hr => mem_moveRecs _ hl hr
    obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := ih v₁ S₁
      (fun j' => BinaryExchangeCall.Ready.updateStream (calls j') S (hready j') l₁.flatten)
      l₁ hl₁ (fun r hr => hlB r (hmem r hr)) (fun r hr => h8 r (hmem r hr)) (by simp [S₁])
    rw [binaryExchangeChainCost_updateStream calls S l₁.flatten js] at hm₂
    refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, ?_, ?_⟩
    · simp only [Nat.cast_add, binaryExchangeChainCost]
      exact add_le_add hm₁ hm₂
    · dsimp only [S₁] at he₂
      simp only [Function.update_idem] at he₂
      exact Exec.seq he₁ he₂

end IntegerMultBounds.MathlibTM2.Routing
