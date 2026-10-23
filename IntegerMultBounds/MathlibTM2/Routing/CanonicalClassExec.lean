module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalDirectionalPair
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRouterClass

/-! Executed false/true/false class routing, with all three concrete metadata
reloads charged and the semantic class permutation as the final record action. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section

variable {Q K : ℕ} (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B) (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (k : Fin 3)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ n)
    (hlen : ∀ row ∈ l, row.length = B ∧ ∀ x ∈ row, x.val < 8)
    (L Lb : ℕ) (rowBits : List Bool)
    (l₁ l₂ : List (List (Fin (prime + K + 4))))
    (hl₁ : l₁.length = R * 2 ^ n) (hl₂ : l₂.length = R * 2 ^ n)
    (hlen₁ : ∀ row ∈ l₁, row.length = B ∧ ∀ x ∈ row, x.val < 8)
    (hlen₂ : ∀ row ∈ l₂, row.length = B ∧ ∀ x ∈ row, x.val < 8)

local notation "stages" => List.finRange (canonicalRouterStride n)
local notation "π₀" => canonicalRouterDirectionalPerm n hn R B hR hB mate hinv k false hQ hA l hl hlen stages
local notation "frame₀" => canonicalDirectionalFrame n hn R B hR hB mate hinv k false hQ hA l hl hlen L Lb rowBits stages
local notation "program₀" => canonicalDirectionalProgram n hn R B hR hB mate hinv k false hQ hA l hl hlen Lb rowBits
local notation "price₀" => canonicalDirectionalPrice n hn R B hR hB mate hinv k false hQ hA l hl hlen L Lb rowBits stages
local notation "π₁" => canonicalRouterDirectionalPerm n hn R B hR hB mate hinv k true hQ hA l₁ hl₁ hlen₁ stages
local notation "frame₁" => canonicalDirectionalFrame n hn R B hR hB mate hinv k true hQ hA l₁ hl₁ hlen₁ L Lb rowBits stages
local notation "program₁" => canonicalDirectionalProgram n hn R B hR hB mate hinv k true hQ hA l₁ hl₁ hlen₁ Lb rowBits
local notation "price₁" => canonicalDirectionalPrice n hn R B hR hB mate hinv k true hQ hA l₁ hl₁ hlen₁ L Lb rowBits stages
local notation "π₂" => canonicalRouterDirectionalPerm n hn R B hR hB mate hinv k false hQ hA l₂ hl₂ hlen₂ stages
local notation "frame₂" => canonicalDirectionalFrame n hn R B hR hB mate hinv k false hQ hA l₂ hl₂ hlen₂ L Lb rowBits stages
local notation "program₂" => canonicalDirectionalProgram n hn R B hR hB mate hinv k false hQ hA l₂ hl₂ hlen₂ Lb rowBits
local notation "price₂" => canonicalDirectionalPrice n hn R B hR hB mate hinv k false hQ hA l₂ hl₂ hlen₂ L Lb rowBits stages
local notation "classPerm" => canonicalRouterClassPerm n hn mate hinv k R B hR hB hQ hA l hl hlen
local notation "src" => framedCoreAux (canonicalRouterCommonT + 3) 0
local notation "saved" => framedCoreAux (canonicalRouterCommonT + 3) 2
local notation "str" => framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream

theorem canonicalClassRecords
    (hnext₁ : l₁ = moveRecs π₀ l) (hnext₂ : l₂ = moveRecs π₁ l₁) :
    moveRecs π₂ l₂ = moveRecs classPerm l := by
  have htrue := (canonicalRouterDirectionalPerm_records_independent n hn mate hinv k R B hR hB hQ hA
    l hl hlen l₁ hl₁ hlen₁ true).symm
  have hfalse := (canonicalRouterDirectionalPerm_records_independent n hn mate hinv k R B hR hB hQ hA
    l hl hlen l₂ hl₂ hlen₂ false).symm
  rw [hfalse, hnext₂, htrue, hnext₁]
  rw [← moveRecs_trans _ _ l hl, ← moveRecs_trans _ _ l hl]
  rfl

theorem canonicalClass_exec
    (hn0 : 0 < n) (hnfit : n < 2 ^ L) (hBfit : B < 2 ^ Lb) (hnB : n ≤ B)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ [])
    (hrowValue : Counter.value rowBits = R)
    (hnext₁ : l₁ = moveRecs π₀ l) (hnext₂ : l₂ = moveRecs π₁ l₁)
    (rest : List (Fin (prime + K + 4)))
    (v : HS ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit)
    (S : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K))
    (ready : FramedCoreReady canonicalDirectionalStream (R * 2 ^ n) B S)
    (hstream : S.R str = l.flatten)
    (hinput : S.R src = frame₀ ++ (frame₁ ++ (frame₂ ++ rest))) :
    let C : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K) :=
      { S with R := delimitedCallAdvanced S.R src saved str frame₀ (frame₁ ++ (frame₂ ++ rest)) l₁.flatten }
    let D : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K) :=
      { C with R := delimitedCallAdvanced C.R src saved str frame₁ (frame₂ ++ rest) l₂.flatten }
    let E : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K) :=
      { D with R := delimitedCallAdvanced D.R src saved str frame₂ rest (moveRecs classPerm l).flatten }
    ∃ (v' : HS ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ (price₀ + price₁) + price₂ ∧
      FramedCoreReady canonicalDirectionalStream (R * 2 ^ n) B E ∧
      Exec Empty.elim (.seq (.seq program₀ program₁) program₂) (mk v S) steps (mk v' E) := by
  dsimp only
  let C : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K) :=
    { S with R := delimitedCallAdvanced S.R src saved str frame₀ (frame₁ ++ (frame₂ ++ rest)) l₁.flatten }
  let D : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K) :=
    { C with R := delimitedCallAdvanced C.R src saved str frame₁ (frame₂ ++ rest) l₂.flatten }
  obtain ⟨v₁, m₁, hu₁, hm₁, hr₁, he₁⟩ := canonicalDirectionalPair_exec n hn R B hR hB mate hinv k false hQ hA
    l hl hlen L Lb rowBits stages k true l₁ hl₁ hlen₁ hn0 hnfit hBfit hnB hrow hrowNe hrowValue hnext₁
    (frame₂ ++ rest) v S ready hstream hinput
  rw [← hnext₂] at hr₁ he₁
  have hsrc : D.R src = frame₂ ++ rest := by
    dsimp only [D, delimitedCallAdvanced]
    rw [Function.update_of_ne (framedCoreEmbed_aux (canonicalRouterCommonT + 3) canonicalDirectionalStream 0).symm,
      Function.update_of_ne ((framedCoreAux_injective (canonicalRouterCommonT + 3)).ne (by decide : (0 : Fin 3) ≠ 2)),
      Function.update_self]
  have hstr : D.R str = l₂.flatten := by
    dsimp only [D, delimitedCallAdvanced]
    exact Function.update_self _ _ _
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := canonicalDirectional_exec n hn R B hR hB mate hinv k false hQ hA
    l₂ hl₂ hlen₂ L Lb rowBits stages hn0 hnfit hBfit hnB hrow hrowNe hrowValue rest v₁ D hr₁ hstr hsrc
  have hr₂ := canonicalDirectional_ready n hn R B hR hB mate hinv k false hQ hA l₂ hl₂ hlen₂
    L Lb rowBits stages rest D hr₁ hstr
  have hout := canonicalClassRecords n hn R B hR hB mate hinv k hQ hA l hl hlen l₁ l₂ hl₁ hl₂ hlen₁ hlen₂ hnext₁ hnext₂
  rw [hout] at he₂ hr₂
  dsimp only [D, C] at he₁ he₂ hr₂
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, ?_, ?_, ?_⟩
  · push_cast
    exact add_le_add hm₁ hm₂
  · exact hr₂
  · exact Exec.seq he₁ he₂

end
end IntegerMultBounds.MathlibTM2.Routing
