module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryExchangeFixedProgram
public import IntegerMultBounds.MathlibTM2.Routing.BinaryScheduleCalls

/-! Fixed placement-chain code for arbitrary stage specifications and row data. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {t₀ m T Q K : ℕ} {P U : Type}

def binaryScheduleFixedCall (slot : BinaryScheduleReg t₀ m → Fin T) (hslot : Function.Injective slot)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd)
    (hQ : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ T) (j : Fin m) : Pr P T Q (prime + K) U :=
  binaryExchangeFixedProgram (slot ∘ binaryScheduleStage j) (hslot.comp (binaryScheduleStage_injective j))
    hd pay hhd hQ hT

def binaryScheduleFixedChain (slot : BinaryScheduleReg t₀ m → Fin T) (hslot : Function.Injective slot)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd)
    (hQ : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ T) : List (Fin m) → Pr P T Q (prime + K) U
  | [] => .act .done
  | j :: js => .seq (binaryScheduleFixedCall slot hslot hd pay hhd hQ hT j)
      (binaryScheduleFixedChain slot hslot hd pay hhd hQ hT js)

theorem binaryScheduleCalls_program {n R B : ℕ}
    (slot : BinaryScheduleReg t₀ m → Fin T) (hslot : Function.Injective slot)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd) (hpay : ∀ k, hd k ≠ pay)
    (hQ : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ T)
    (spec : Fin m → BlockExchangeSpec n) (hR : 0 < R) (hB : 0 < B)
    (rowBits : List Bool) (Lc L : ℕ) (hn : n < 2 ^ Lc) (hBin : B < 2 ^ L)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ []) (hrowValue : Counter.value rowBits = R)
    (j : Fin m) :
    ((binaryScheduleCalls slot hslot hd pay hhd hpay hQ hT spec hR hB rowBits Lc L hn hBin
      hrow hrowNe hrowValue j).program : Pr P T Q (prime + K) U) =
      binaryScheduleFixedCall slot hslot hd pay hhd hQ hT j := rfl

theorem binaryScheduleCalls_chain {n R B : ℕ}
    (slot : BinaryScheduleReg t₀ m → Fin T) (hslot : Function.Injective slot)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd) (hpay : ∀ k, hd k ≠ pay)
    (hQ : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ T)
    (spec : Fin m → BlockExchangeSpec n) (hR : 0 < R) (hB : 0 < B)
    (rowBits : List Bool) (Lc L : ℕ) (hn : n < 2 ^ Lc) (hBin : B < 2 ^ L)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ []) (hrowValue : Counter.value rowBits = R)
    (js : List (Fin m)) :
    (binaryExchangeChain (binaryScheduleCalls slot hslot hd pay hhd hpay hQ hT spec hR hB rowBits Lc L hn hBin
      hrow hrowNe hrowValue) js : Pr P T Q (prime + K) U) =
      binaryScheduleFixedChain slot hslot hd pay hhd hQ hT js := by
  induction js with
  | nil => rfl
  | cons j js ih => rw [binaryExchangeChain, binaryScheduleFixedChain, binaryScheduleCalls_program, ih]

end
end IntegerMultBounds.MathlibTM2.Routing
