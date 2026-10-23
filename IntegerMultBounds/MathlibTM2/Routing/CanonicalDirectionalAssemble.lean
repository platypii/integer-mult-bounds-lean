module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalDirectionalExec

/-! A live directional bank is serialized, cleared and then routed through the
existing loader. Upstream production of that bank remains a separate phase. -/

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


local notation "bank" => canonicalDirectionalBank n hn R B hR hB mate hinv k reverse hQ hA l hl hlen L Lb rowBits stages


local notation "frame" => canonicalDirectionalFrame n hn R B hR hB mate hinv k reverse hQ hA l hl hlen L Lb rowBits stages
local notation "program" => canonicalDirectionalProgram n hn R B hR hB mate hinv k reverse hQ hA l hl hlen Lb rowBits
local notation "price" => canonicalDirectionalPrice n hn R B hR hB mate hinv k reverse hQ hA l hl hlen L Lb rowBits stages
local notation "fields" => framedCoreDestinations (framedCoreEmbed (canonicalRouterCommonT + 3)) canonicalDirectionalStream
local notation "src" => framedCoreAux (canonicalRouterCommonT + 3) 0
local notation "tmp" => framedCoreAux (canonicalRouterCommonT + 3) 1
local notation "saved" => framedCoreAux (canonicalRouterCommonT + 3) 2
local notation "str" => framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream
local notation "output" => List.flatten (moveRecs (canonicalRouterDirectionalPerm n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages) l)

theorem canonicalDirectional_assemble_exec
    (hn0 : 0 < n) (hnfit : n < 2 ^ L) (hBfit : B < 2 ^ Lb) (hnB : n ≤ B)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ [])
    (hrowValue : Counter.value rowBits = R)
    (v : HS ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit)
    (S : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K))
    (hleft : ∀ j, S.L (framedCoreEmbed (canonicalRouterCommonT + 3) j) = [])
    (hbank : ∀ j, j ≠ canonicalDirectionalStream → S.R (framedCoreEmbed (canonicalRouterCommonT + 3) j) = bank j)
    (htmp : S.R tmp = []) (hsaved : S.R saved = []) (hstream : S.R str = l.flatten) :
    let C : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K) :=
      { S with R := Function.update (metadataCleared S.R fields) src (frame ++ S.R src) }
    let E : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K) :=
      { C with R := delimitedCallAdvanced C.R src saved str frame (S.R src) output }
    ∃ (v' : HS ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ (9 * (frame).length + 2 : ℕ) + price ∧
      FramedCoreReady canonicalDirectionalStream (R * 2 ^ n) B E ∧
      Exec Empty.elim (.seq (.seq (delimitedConfigurationWrite canonicalDirectionalOuterDelimiter src tmp saved fields)
        (metadataClean fields)) program) (mk v S) steps (mk v' E) := by
  dsimp only
  let C : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K) :=
    { S with R := Function.update (metadataCleared S.R fields) src (frame ++ S.R src) }
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := canonicalDirectionalFrameWriteClean_exec n hn R B hR hB mate hinv k reverse hQ hA l hl hlen
    L Lb rowBits stages v S hbank htmp hsaved
  have hr₁ := framedCoreWriteClean_ready canonicalDirectionalStream S frame hleft htmp l hl hlen hstream
  have hc : C.R src = frame ++ S.R src := by
    dsimp only [C]
    exact Function.update_self _ _ _
  have ht : C.R str = l.flatten := by
    dsimp only [C]
    rw [Function.update_of_ne (framedCoreEmbed_aux (canonicalRouterCommonT + 3) canonicalDirectionalStream 0),
      metadataCleared_keep _ _ _ (framedCoreDestinations_stream _ (framedCoreEmbed_injective (canonicalRouterCommonT + 3)) canonicalDirectionalStream)]
    exact hstream
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := canonicalDirectional_exec n hn R B hR hB mate hinv k reverse hQ hA l hl hlen
    L Lb rowBits stages hn0 hnfit hBfit hnB hrow hrowNe hrowValue (S.R src) v₁ C hr₁ ht hc
  have hr₂ := canonicalDirectional_ready n hn R B hR hB mate hinv k reverse hQ hA l hl hlen
    L Lb rowBits stages (S.R src) C hr₁ ht
  dsimp only [C] at he₁ he₂ hr₂
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, ?_, hr₂, Exec.seq he₁ he₂⟩
  push_cast
  exact add_le_add (by exact_mod_cast hm₁) hm₂

end
end IntegerMultBounds.MathlibTM2.Routing
