module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalMatchingInput

/-! Rewind the supplied outer metadata after all nine directions. Every tape
except the routed record stream returns to its original contents. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section

theorem delimitedCallAdvanced_rewind {T A : ℕ} (src saved str : Fin T)
    (hsa : src ≠ saved) (hss : src ≠ str) (has : saved ≠ str)
    (R : Fin T → List (Fin (A + 4))) (frame output : List (Fin (A + 4)))
    (hsrc : R src = frame) (hsaved : R saved = []) :
    let C := delimitedCallAdvanced R src saved str frame [] output
    movedR C saved src id (C saved) = Function.update R str output := by
  dsimp only
  funext j
  by_cases hs : j = src
  · subst j
    simp [movedR, delimitedCallAdvanced, hsa, hss, has, hsrc, hsaved]
  · by_cases ha : j = saved
    · subst j
      simp [movedR, delimitedCallAdvanced, hs, has, hsaved]
    · by_cases ht : j = str
      · subst j
        simp [movedR, delimitedCallAdvanced, hs, ha]
      · simp [movedR, delimitedCallAdvanced, hs, ha, ht]

variable {Q K : ℕ} (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B) (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ n)
    (hlen : ∀ row ∈ l, row.length = B ∧ ∀ x ∈ row, x.val < 8)
    (L Lb : ℕ) (rowBits : List Bool)

local notation "frame" => canonicalMatchingFrame n hn R B hR hB mate hinv hQ hA l hl hlen L Lb rowBits
local notation "program" => canonicalMatchingProgram n hn R B hR hB mate hinv hQ hA l hl hlen Lb rowBits
local notation "price" => canonicalMatchingPrice n hn R B hR hB mate hinv hQ hA l hl hlen L Lb rowBits
local notation "output" => List.flatten (moveRecs (canonicalRouterMatchingPerm n hn mate hinv R B hR hB hQ hA l hl hlen) l)
local notation "src" => framedCoreAux (canonicalRouterCommonT + 3) 0
local notation "saved" => framedCoreAux (canonicalRouterCommonT + 3) 2
local notation "str" => framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream

theorem canonicalMatching_restored_exec
    (hn0 : 0 < n) (hnfit : n < 2 ^ L) (hBfit : B < 2 ^ Lb) (hnB : n ≤ B)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ [])
    (hrowValue : Counter.value rowBits = R)
    (v : HS ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit)
    (S : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K))
    (ready : FramedCoreReady canonicalDirectionalStream (R * 2 ^ n) B S)
    (hstream : S.R str = l.flatten) (hinput : S.R src = frame) (hsaved : S.R saved = []) :
    ∃ (v' : HS ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ price + (2 * (frame).length + 2 : ℕ) ∧
      Exec Empty.elim (.seq program (moveR saved src id)) (mk v S) steps
        (mk v' { S with R := Function.update S.R str output }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, _, he₁⟩ := canonicalMatchingInput_exec n hn R B hR hB mate hinv hQ hA l hl hlen
    L Lb rowBits hn0 hnfit hBfit hnB hrow hrowNe hrowValue [] v S ready hstream (by simpa using hinput)
  let C : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K) :=
    { S with R := delimitedCallAdvanced S.R src saved str frame [] output }
  have hsa : src ≠ saved := (framedCoreAux_injective (canonicalRouterCommonT + 3)).ne (by decide)
  have hss : src ≠ str := (framedCoreEmbed_aux (canonicalRouterCommonT + 3) canonicalDirectionalStream 0).symm
  have has : saved ≠ str := (framedCoreEmbed_aux (canonicalRouterCommonT + 3) canonicalDirectionalStream 2).symm
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec Empty.elim saved src hsa.symm id v₁ C
  have hf := delimitedCallAdvanced_rewind src saved str hsa hss has S.R frame output hinput hsaved
  have ha : C.R saved = (frame).reverse := by
    simp only [C, delimitedCallAdvanced, Function.update_of_ne has, Function.update_self, hsaved, List.append_nil]
  dsimp only at hf
  dsimp only [C] at he₂ ha
  rw [hf, ha, List.length_reverse] at he₂
  refine ⟨v₂, m₁ + (2 * (frame).length + 2), hu₂.trans hu₁, ?_, Exec.seq he₁ he₂⟩
  push_cast
  exact add_le_add hm₁ (le_refl _)

end
end IntegerMultBounds.MathlibTM2.Routing
