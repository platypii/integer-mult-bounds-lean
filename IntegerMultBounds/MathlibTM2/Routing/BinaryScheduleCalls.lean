module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryScheduleLayout
public import IntegerMultBounds.MathlibTM2.Routing.BinaryExchangeChain

/-! Actual schedule calls all backed by one common binary-input bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable def binaryScheduleCalls {t₀ m T Q n R B : ℕ}
    (slot : BinaryScheduleReg t₀ m → Fin T) (hslot : Function.Injective slot)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd) (hpay : ∀ k, hd k ≠ pay)
    (hQ : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ T)
    (spec : Fin m → BlockExchangeSpec n) (hR : 0 < R) (hB : 0 < B)
    (rowBits : List Bool) (Lc L : ℕ) (hn : n < 2 ^ Lc) (hBin : B < 2 ^ L)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ []) (hrowValue : Counter.value rowBits = R) :
    Fin m → BinaryExchangeCall t₀ T Q n R B (slot .str) (slot .tmp) := fun j =>
  binaryExchangeLayoutCall (slot ∘ binaryScheduleStage j) (hslot.comp (binaryScheduleStage_injective j))
    hd pay hhd hpay hQ hT (spec j) hR hB rowBits Lc L hn hBin hrow hrowNe hrowValue

theorem binaryScheduleCalls_cost_le {t₀ m T Q K n R B : ℕ}
    (slot : BinaryScheduleReg t₀ m → Fin T) (hslot : Function.Injective slot)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd) (hpay : ∀ k, hd k ≠ pay)
    (hQ : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ T)
    (spec : Fin m → BlockExchangeSpec n) (hR : 0 < R) (hB : 0 < B)
    (rowBits : List Bool) (Lc L : ℕ) (hn : n < 2 ^ Lc) (hBin : B < 2 ^ L)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ []) (hrowValue : Counter.value rowBits = R)
    (S : Stacks T (prime + K)) (hbank : ∀ i, S.R (slot (.bank i)) = []) (j : Fin m) :
    (binaryScheduleCalls slot hslot hd pay hhd hpay hQ hT spec hR hB rowBits Lc L hn hBin hrow hrowNe hrowValue j).cost S ≤
      3 * swapConst * (T + 12 * swapT t₀ + 5 : ℕ) * (R * 2 ^ n * B : ℕ) *
        ((max 1 (spec j).w : ℕ) : ℝ) ^ Parameters.tau +
      (generatedExchangeUniformOverhead t₀ T n R B L rowBits.length Lc 0 +
        (3 * (Lc * (4 * n + 31) + 2 * n + 26) + 10 * Lc + 12) + (2 * n + 2 * Lc + 9) : ℕ) := by
  let c := binaryScheduleCalls slot hslot hd pay hhd hpay hQ hT spec hR hB
    rowBits Lc L hn hBin hrow hrowNe hrowValue j
  have hb : (∑ i, (S.R (c.bank i)).length) ≤ 0 := by
    change (∑ i : Fin (swapT t₀), (S.R (slot (.bank i))).length) ≤ 0
    simp only [hbank, List.length_nil, Finset.sum_const_zero, le_refl]
  exact c.cost_uniform_overhead S L rowBits.length Lc 0 (le_refl _) (le_refl _) (le_refl _) hb

theorem binaryScheduleChainCost_le {t₀ m T Q K n R B : ℕ}
    (slot : BinaryScheduleReg t₀ m → Fin T) (hslot : Function.Injective slot)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd) (hpay : ∀ k, hd k ≠ pay)
    (hQ : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ T)
    (spec : Fin m → BlockExchangeSpec n) (hR : 0 < R) (hB : 0 < B)
    (rowBits : List Bool) (Lc L : ℕ) (hn : n < 2 ^ Lc) (hBin : B < 2 ^ L)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ []) (hrowValue : Counter.value rowBits = R)
    (S : Stacks T (prime + K)) (hbank : ∀ i, S.R (slot (.bank i)) = []) (js : List (Fin m)) :
    binaryExchangeChainCost
      (binaryScheduleCalls slot hslot hd pay hhd hpay hQ hT spec hR hB rowBits Lc L hn hBin hrow hrowNe hrowValue) S js ≤
      (3 * swapConst * (T + 12 * swapT t₀ + 5 : ℕ) * (R * 2 ^ n * B : ℕ)) *
        (js.map (fun j => ((max 1 (spec j).w : ℕ) : ℝ) ^ Parameters.tau)).sum +
      js.length * (generatedExchangeUniformOverhead t₀ T n R B L rowBits.length Lc 0 +
        (3 * (Lc * (4 * n + 31) + 2 * n + 26) + 10 * Lc + 12) + (2 * n + 2 * Lc + 9) : ℕ) + 1 := by
  apply binaryExchangeChainCost_le_sum
  intro j _
  exact binaryScheduleCalls_cost_le slot hslot hd pay hhd hpay hQ hT spec hR hB
    rowBits Lc L hn hBin hrow hrowNe hrowValue S hbank j

theorem binaryScheduleCalls_spec {t₀ m T Q n R B : ℕ}
    (slot : BinaryScheduleReg t₀ m → Fin T) (hslot : Function.Injective slot)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd) (hpay : ∀ k, hd k ≠ pay)
    (hQ : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ T)
    (spec : Fin m → BlockExchangeSpec n) (hR : 0 < R) (hB : 0 < B)
    (rowBits : List Bool) (Lc L : ℕ) (hn : n < 2 ^ Lc) (hBin : B < 2 ^ L)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ []) (hrowValue : Counter.value rowBits = R)
    (j : Fin m) :
    (binaryScheduleCalls slot hslot hd pay hhd hpay hQ hT spec hR hB rowBits Lc L hn hBin hrow hrowNe hrowValue j).spec = spec j := by
  rfl

theorem binaryScheduleCalls_ready {t₀ m T Q K n R B : ℕ}
    (slot : BinaryScheduleReg t₀ m → Fin T) (hslot : Function.Injective slot)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd) (hpay : ∀ k, hd k ≠ pay)
    (hQ : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ T)
    (spec : Fin m → BlockExchangeSpec n) (hR : 0 < R) (hB : 0 < B)
    (rowBits : List Bool) (Lc L : ℕ) (hn : n < 2 ^ Lc) (hBin : B < 2 ^ L)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ []) (hrowValue : Counter.value rowBits = R)
    (bankWords : Fin (swapT t₀) → List (Fin (prime + K + 4)))
    (hpay0 : bankWords (reg pay) = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → bankWords j = [])
    (hhdr0 : ∀ k, bankWords (reg (hd k)) = [])
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ s ∈ bankWords (reg i), s ≠ blank ∧ s.val < prime + 4)
    (S : Stacks T (prime + K)) (hL : ∀ j, S.L j = []) (stream : List (Fin (prime + K + 4)))
    (hinput : ∀ r, S.R (slot r) = binaryScheduleInputWords spec bankWords Lc L B rowBits stream r) (j : Fin m) :
    (binaryScheduleCalls slot hslot hd pay hhd hpay hQ hT spec hR hB rowBits Lc L hn hBin hrow hrowNe hrowValue j).Ready S := by
  apply binaryExchangeLayoutCall_ready (slot ∘ binaryScheduleStage j) (hslot.comp (binaryScheduleStage_injective j))
    hd pay hhd hpay hQ hT (spec j) hR hB rowBits Lc L hn hBin hrow hrowNe hrowValue
    bankWords hpay0 hpriv hhdr0 hother S hL stream
  intro r
  change S.R (slot (binaryScheduleStage j r)) = _
  rw [hinput, binaryScheduleInputWords_stage]

end IntegerMultBounds.MathlibTM2.Routing
