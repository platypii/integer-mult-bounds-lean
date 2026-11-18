module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackSwapMachine
public import IntegerMultBounds.MathlibTM2.Host.Foreign

/-! Execute the prepared coordinate swap on host stacks representing its tape bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open RecursiveInterchangeLayout (volume)
open M8.RevMachine
open SharedBankStageInput (raw)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos w).ne'⟩

theorem swapPayload_exec [M8.Machine.Net] {T d w W : ℕ} {P U : Type}
    (i j : Fin d) (h : i < j) (hw : 0 < w) (hW : 0 < W)
    (roles : Tapes T prime) (io : Fin T)
    (x : Fin (volume prime (payloadView prime d w W)) → ZMod 2)
    (hh : roles.head io = 0) (hx : roles.tape io = sourceWord x) :
    let view := payloadView prime d w W
    let headers := LabelPrepare.input view d i.val j.val w
    let block := LabelSwap.program io
    let cost := 3808274 * volume prime view + LeafCore.coreCost (volume prime view) w
    ∀ (body : P → Pr P block.tapes block.states prime U) (v : HS block.tapes block.states prime U)
      (S : Stacks block.tapes prime),
      RepT (raw (LabelCall.bank roles view headers) block.tapes) S.L S.R →
      ∃ (y : Fin (volume prime view) → ZMod 2), ∃ z F n, z.user = v.user ∧ n ≤ cost*(block.tapes+5)+6 ∧
        Exec body (foreign block.program) (mk v S) n (mk z F) ∧
        RepT (raw (LabelCall.bank (SharedPlacementAlphabet.setTape roles io (sourceWord (v := view) y) 0)
          view headers) block.tapes) F.L F.R ∧
        ∀ (coords : Fin d → ZMod (prime^w)) (k : Fin W),
          ext y (FlatCoordinateLayout.index (coords ∘ Equiv.swap i j) k).val =
            ext x (FlatCoordinateLayout.index coords k).val := by
  intro view headers block cost body v S ready
  obtain ⟨y,swap,effect⟩ := swapPayload_runs i j h hw hW roles io x hh hx
  obtain ⟨z,F,_,rfl,rep,user,_,_,_,n,time,run⟩ := foreign_exec body block.program swap v S _ rfl ready
  exact ⟨y,z,F,n,user,time,run,rep,effect⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
