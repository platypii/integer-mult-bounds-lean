module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryExchangeLayoutCall

/-! Interval dimensions, row counts and binary widths are proof/data annotations
of binary exchange calls. Their executable code depends only on fixed registers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {t₀ T Q K : ℕ} {P U : Type}

def binaryExchangeFixedProgram (slot : BinaryExchangeReg t₀ → Fin T) (hslot : Function.Injective slot)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd)
    (hQ : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ T) : Pr P T Q (prime + K) U :=
  .seq (exchangeBinarySetupProgram (slot ∘ binaryExchangeExponentReg) (slot .canonical))
    (.seq (.seq (exchangeHeaderProgram (slot ∘ binaryExchangeHeaderReg))
      (.seq (installedBlockExchangeProgram (fun k => slot (.header k)) (fun j => slot (.bank j)) hd
        (slot .work) (slot .aux) (slot .ctmp)
        (swapPass hd pay hhd hQ (fun j => slot (.bank j))
          (hslot.comp (by intro i j h; exact BinaryExchangeReg.bank.inj h)) hT (slot .str) (slot .tmp)))
        (metadataClean (exchangeHeaderPrivate (slot ∘ binaryExchangeHeaderReg)))))
      (metadataClean (exchangeBinarySetupPrivate (slot ∘ binaryExchangeExponentReg) (slot .canonical))))

theorem binaryExchangeLayoutCall_program {n R B : ℕ}
    (slot : BinaryExchangeReg t₀ → Fin T) (hslot : Function.Injective slot)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd) (hpay : ∀ k, hd k ≠ pay)
    (hQ : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ T)
    (spec : BlockExchangeSpec n) (hR : 0 < R) (hB : 0 < B)
    (rowBits : List Bool) (Lc L : ℕ) (hn : n < 2 ^ Lc) (hBin : B < 2 ^ L)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ []) (hrowValue : Counter.value rowBits = R) :
    ((binaryExchangeLayoutCall slot hslot hd pay hhd hpay hQ hT spec hR hB rowBits Lc L hn hBin
      hrow hrowNe hrowValue).program : Pr P T Q (prime + K) U) =
      binaryExchangeFixedProgram slot hslot hd pay hhd hQ hT := rfl

end
end IntegerMultBounds.MathlibTM2.Routing
