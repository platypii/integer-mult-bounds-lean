module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalDirectionalExec

/-! Two concrete direction calls consume successive frames on the same bank.
Both reloads and cleanups are executed, with the unused suffix preserved. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section

variable {Q K : ℕ} (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B) (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (k : Fin 3) (reverse : Bool)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ n)
    (hlen : ∀ row ∈ l, row.length = B ∧ ∀ x ∈ row, x.val < 8)
    (L Lb : ℕ) (rowBits : List Bool) (stages : List (Fin (canonicalRouterStride n)))



variable (k' : Fin 3) (reverse' : Bool)
    (l' : List (List (Fin (prime + K + 4)))) (hl' : l'.length = R * 2 ^ n)
    (hlen' : ∀ row ∈ l', row.length = B ∧ ∀ x ∈ row, x.val < 8)

local notation "π" => canonicalRouterDirectionalPerm n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages
local notation "π'" => canonicalRouterDirectionalPerm n hn R B hR hB mate hinv k' reverse' hQ hA l' hl' hlen' stages
local notation "frame" => canonicalDirectionalFrame n hn R B hR hB mate hinv k reverse hQ hA l hl hlen L Lb rowBits stages
local notation "frame'" => canonicalDirectionalFrame n hn R B hR hB mate hinv k' reverse' hQ hA l' hl' hlen' L Lb rowBits stages
local notation "program" => canonicalDirectionalProgram n hn R B hR hB mate hinv k reverse hQ hA l hl hlen Lb rowBits
local notation "program'" => canonicalDirectionalProgram n hn R B hR hB mate hinv k' reverse' hQ hA l' hl' hlen' Lb rowBits
local notation "price" => canonicalDirectionalPrice n hn R B hR hB mate hinv k reverse hQ hA l hl hlen L Lb rowBits stages
local notation "price'" => canonicalDirectionalPrice n hn R B hR hB mate hinv k' reverse' hQ hA l' hl' hlen' L Lb rowBits stages
local notation "src" => framedCoreAux (canonicalRouterCommonT + 3) 0
local notation "saved" => framedCoreAux (canonicalRouterCommonT + 3) 2
local notation "str" => framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream

theorem canonicalDirectionalPair_exec
    (hn0 : 0 < n) (hnfit : n < 2 ^ L) (hBfit : B < 2 ^ Lb) (hnB : n ≤ B)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ [])
    (hrowValue : Counter.value rowBits = R) (hnext : l' = moveRecs π l)
    (rest : List (Fin (prime + K + 4)))
    (v : HS ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit)
    (S : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K))
    (ready : FramedCoreReady canonicalDirectionalStream (R * 2 ^ n) B S)
    (hstream : S.R str = l.flatten) (hinput : S.R src = frame ++ (frame' ++ rest)) :
    let C : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K) :=
      { S with R := delimitedCallAdvanced S.R src saved str frame (frame' ++ rest) l'.flatten }
    let D : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K) :=
      { C with R := delimitedCallAdvanced C.R src saved str frame' rest (moveRecs π' l').flatten }
    ∃ (v' : HS ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ price + price' ∧
      FramedCoreReady canonicalDirectionalStream (R * 2 ^ n) B D ∧
      Exec Empty.elim (.seq program program') (mk v S) steps (mk v' D) := by
  dsimp only
  let C : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K) :=
    { S with R := delimitedCallAdvanced S.R src saved str frame (frame' ++ rest) l'.flatten }
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := canonicalDirectional_exec n hn R B hR hB mate hinv k reverse hQ hA l hl hlen
    L Lb rowBits stages hn0 hnfit hBfit hnB hrow hrowNe hrowValue (frame' ++ rest) v S ready hstream hinput
  have hr₁ := canonicalDirectional_ready n hn R B hR hB mate hinv k reverse hQ hA l hl hlen
    L Lb rowBits stages (frame' ++ rest) S ready hstream
  rw [← hnext] at he₁ hr₁
  have hsrc : C.R src = frame' ++ rest := by
    dsimp only [C, delimitedCallAdvanced]
    rw [Function.update_of_ne (framedCoreEmbed_aux (canonicalRouterCommonT + 3) canonicalDirectionalStream 0).symm,
      Function.update_of_ne ((framedCoreAux_injective (canonicalRouterCommonT + 3)).ne (by decide : (0 : Fin 3) ≠ 2)),
      Function.update_self]
  have hstr : C.R str = l'.flatten := by
    dsimp only [C, delimitedCallAdvanced]
    exact Function.update_self _ _ _
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := canonicalDirectional_exec n hn R B hR hB mate hinv k' reverse' hQ hA l' hl' hlen'
    L Lb rowBits stages hn0 hnfit hBfit hnB hrow hrowNe hrowValue rest v₁ C hr₁ hstr hsrc
  have hr₂ := canonicalDirectional_ready n hn R B hR hB mate hinv k' reverse' hQ hA l' hl' hlen'
    L Lb rowBits stages rest C hr₁ hstr
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, ?_, hr₂, Exec.seq he₁ he₂⟩
  push_cast
  exact add_le_add hm₁ hm₂

end
end IntegerMultBounds.MathlibTM2.Routing
