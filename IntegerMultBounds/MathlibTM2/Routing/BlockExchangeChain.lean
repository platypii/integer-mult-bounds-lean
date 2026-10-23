module

public import IntegerMultBounds.MathlibTM2.Routing.BlockExchangeExec

/-!
# Priced composition of prepared interval interchanges

Every actual exchange restores all registers except the shared stream. Therefore
all later prepared banks survive unchanged, and a structural schedule composes
without fresh per-stage execution assumptions. Raw header generation is not
provided by this theorem.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

structure BlockExchangeSpec (n : ℕ) where
  a : ℕ
  b : ℕ
  w : ℕ
  separate : a + w ≤ b
  fits : b + w ≤ n

def BlockExchangeSpec.rank {n : ℕ} (s : BlockExchangeSpec n) (R : ℕ) :=
  blockExchangeRank n s.a s.b s.w R s.separate s.fits

def BlockExchangeSpec.coordinate {n : ℕ} (s : BlockExchangeSpec n) :=
  blockExchangePerm n s.a s.b s.w s.separate s.fits

theorem BlockExchangeSpec.rank_row {n : ℕ} (s : BlockExchangeSpec n) (R : ℕ)
    (i : Fin (R * 2 ^ n)) : (s.rank R i).val / 2 ^ n = i.val / 2 ^ n :=
  blockExchangeIdx_div n s.a s.b s.w s.separate s.fits i.val

theorem BlockExchangeSpec.rank_bit {n : ℕ} (s : BlockExchangeSpec n) (R : ℕ)
    (i : Fin (R * 2 ^ n)) (q : Fin n) :
    (s.rank R i).val.testBit q.val = i.val.testBit (s.coordinate q).val :=
  blockExchangeRank_bit n s.a s.b s.w R s.separate s.fits i q

def exchangeChainData {J : Type*} {n R : ℕ} (spec : J → BlockExchangeSpec n) :
    List J → List (List α) → List (List α)
  | [], l => l
  | j :: js, l => exchangeChainData (R := R) spec js (moveRecs ((spec j).rank R) l)

variable {J : Type*} {t₀ T Q K : ℕ} {U F : Type}

noncomputable def exchangeChain
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd)
    (hQ : swapStates hd pay hhd ≤ Q)
    (bank : J → Fin (swapT t₀) → Fin T) (hbank : ∀ j, Function.Injective (bank j))
    (hT : swapT t₀ ≤ T) (str tmp : Fin T) : List J → Pr F T Q (prime + K) U
  | [] => .act .done
  | j :: js => .seq (swapPass hd pay hhd hQ (bank j) (hbank j) hT str tmp)
      (exchangeChain hd pay hhd hQ bank hbank hT str tmp js)

noncomputable def exchangeStepCost {n : ℕ} (spec : J → BlockExchangeSpec n)
    (bank : J → Fin (swapT t₀) → Fin T) (R B : ℕ)
    (S : Stacks T (prime + K)) (j : J) : ℝ :=
  3 * swapConst * (T + 12 * swapT t₀ + 5 : ℕ) * (R * 2 ^ n * B : ℕ) *
    ((max 1 (spec j).w : ℕ) : ℝ) ^ Parameters.tau +
    (6 * ∑ k, (S.R (bank j k)).length + 34 * (R * 2 ^ n * B) +
      2 * T + 6 * swapT t₀ + 23 : ℕ)

noncomputable def exchangeChainCost {n : ℕ} (spec : J → BlockExchangeSpec n)
    (bank : J → Fin (swapT t₀) → Fin T) (R B : ℕ)
    (S : Stacks T (prime + K)) : List J → ℝ
  | [] => 1
  | j :: js => exchangeStepCost spec bank R B S j + exchangeChainCost spec bank R B S js

/-- Execute the complete schedule from initially prepared banks. Each stage is
proved by the actual host theorem; none is supplied as an execution oracle. -/
theorem exchangeChain_exec {n R B : ℕ} (spec : J → BlockExchangeSpec n)
    (body : F → Pr F T Q (prime + K) U)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd)
    (hQ : swapStates hd pay hhd ≤ Q)
    (bank : J → Fin (swapT t₀) → Fin T) (hbank : ∀ j, Function.Injective (bank j))
    (hT : swapT t₀ ≤ T) (str tmp : Fin T) (hst : str ≠ tmp)
    (hstr : ∀ j k, bank j k ≠ str) (htmp : ∀ j k, bank j k ≠ tmp)
    (hR : 0 < R) (hB : 0 < B) (hs : J → Fin 5 → List Bool)
    (hv : ∀ j k, Counter.value (hs j k) = swapValues
      (blockExchangeDimensions n (spec j).a (spec j).b (spec j).w R B).1
      (blockExchangeDimensions n (spec j).a (spec j).b (spec j).w R B).2.1
      (blockExchangeDimensions n (spec j).a (spec j).b (spec j).w R B).2.2
      (spec j).w (spec j).w k)
    (hc : ∀ j k, GrowingCounterData.Canonical (hs j k))
    (js : List J) (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (hL : ∀ k, S.L k = []) (htmp0 : S.R tmp = [])
    (hpay0 : ∀ j, S.R (bank j (reg pay)) = [])
    (hpriv : ∀ j k, t₀ ≤ k.val → S.R (bank j k) = [])
    (hhdr : ∀ j k, S.R (bank j (reg (hd k))) = separator :: (hs j k).map bitSymbol)
    (hother : ∀ j i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (bank j (reg i)), s ≠ blank ∧ s.val < prime + 4)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ n)
    (hlB : ∀ r ∈ l, r.length = B) (h8 : ∀ r ∈ l, ∀ s ∈ r, s.val < 8)
    (hsrc : S.R str = l.flatten) :
    ∃ (v' : HS T Q (prime + K) U) (m : ℕ), v'.user = v.user ∧
      (m : ℝ) ≤ exchangeChainCost spec bank R B S js ∧
      Exec body (exchangeChain hd pay hhd hQ bank hbank hT str tmp js) (mk v S) m
        (mk v' { S with R := Function.update S.R str (exchangeChainData (R := R) spec js l).flatten }) := by
  induction js generalizing v S l with
  | nil =>
    refine ⟨v, 1, rfl, by simp [exchangeChainCost], ?_⟩
    have he : Function.update S.R str l.flatten = S.R := by rw [← hsrc, Function.update_eq_self]
    simpa only [exchangeChain, exchangeChainData, he, run_done] using
      (Exec.act (body := body) .done (mk v S))
  | cons j js ih =>
    obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := blockExchange_exec body hd pay hhd hQ
      (bank j) (hbank j) hT str tmp hst (hstr j) (htmp j)
      n (spec j).a (spec j).b (spec j).w (spec j).separate (spec j).fits
      hR hB l hl hlB h8 (hs j) (hv j) (hc j) v S hL hsrc htmp0 (hpay0 j)
      (hpriv j) (hhdr j) (hother j)
    let l₁ := moveRecs ((spec j).rank R) l
    let S₁ : Stacks T (prime + K) := { S with R := Function.update S.R str l₁.flatten }
    have hkeep (j' : J) (k : Fin (swapT t₀)) : S₁.R (bank j' k) = S.R (bank j' k) :=
      Function.update_of_ne (hstr j' k) _ _
    have hl₁ : l₁.length = R * 2 ^ n := length_moveRecs _ _
    have hmem : ∀ r ∈ l₁, r ∈ l := fun r hr => mem_moveRecs _ hl hr
    obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := ih v₁ S₁ (by exact hL)
      (by dsimp [S₁]; rw [Function.update_of_ne hst.symm]; exact htmp0)
      (by intro j'; rw [hkeep]; exact hpay0 j')
      (by intro j' k hk; rw [hkeep]; exact hpriv j' k hk)
      (by intro j' k; rw [hkeep]; exact hhdr j' k)
      (by intro j' i hi hh; rw [hkeep]; exact hother j' i hi hh)
      l₁ hl₁ (fun r hr => hlB r (hmem r hr))
      (fun r hr => h8 r (hmem r hr)) (by simp [S₁])
    have hcost_all (ks : List J) :
        exchangeChainCost spec bank R B S₁ ks = exchangeChainCost spec bank R B S ks := by
      induction ks with
      | nil => rfl
      | cons j' ks ih' => simp only [exchangeChainCost, exchangeStepCost, hkeep, ih']
    rw [hcost_all js] at hm₂
    refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, ?_, ?_⟩
    · change ((m₁ + m₂ : ℕ) : ℝ) ≤ exchangeStepCost spec bank R B S j + _
      dsimp only [exchangeStepCost]
      rw [Nat.cast_add]
      exact add_le_add hm₁ hm₂
    · have he₂' := he₂
      dsimp only [S₁] at he₂'
      simp only [Function.update_idem] at he₂'
      exact Exec.seq he₁ he₂'

end IntegerMultBounds.MathlibTM2.Routing
