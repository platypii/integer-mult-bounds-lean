module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalPermutationRank

/-! Eighteen executed directions for an arbitrary coordinate permutation.
The explicit metadata frame is supplied; all loading, routing and rewind are charged. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section

variable {Q K : ℕ} (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B) (f : Equiv.Perm (Fin n))
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ n)
    (hlen : ∀ row ∈ l, row.length = B ∧ ∀ x ∈ row, x.val < 8)

attribute [local irreducible] canonicalRouterMatchingPerm canonicalRouterClassPerm canonicalRouterDirectionalPerm

local notation "a" => permutationReflection f
local notation "b" => fun q => f (permutationReflection f q)
local notation "ha" => And.left (permutation_two_matchings f)
local notation "hb" => And.left (And.right (permutation_two_matchings f))
local notation "π" => canonicalRouterMatchingPerm n hn b hb R B hR hB hQ hA l hl hlen


local notation "middle" => canonicalPermutationMiddle n hn R B hR hB f hQ hA l hl hlen
local notation "middleCount" => canonicalPermutationMiddle_count n hn R B hR hB f hQ hA l hl hlen
local notation "middleShape" => canonicalPermutationMiddle_shape n hn R B hR hB f hQ hA l hl hlen
local notation "σ" => canonicalRouterMatchingPerm n hn a ha R B hR hB hQ hA middle middleCount middleShape
local notation "rank" => canonicalPermutationRank n hn R B hR hB f hQ hA l hl hlen
variable (L Lb : ℕ) (rowBits : List Bool)
local notation "frame₀" => canonicalMatchingFrame n hn R B hR hB b hb hQ hA l hl hlen L Lb rowBits
local notation "frame₁" => canonicalMatchingFrame n hn R B hR hB a ha hQ hA middle middleCount middleShape L Lb rowBits
local notation "program₀" => canonicalMatchingProgram n hn R B hR hB b hb hQ hA l hl hlen Lb rowBits
local notation "program₁" => canonicalMatchingProgram n hn R B hR hB a ha hQ hA middle middleCount middleShape Lb rowBits
local notation "price₀" => canonicalMatchingPrice n hn R B hR hB b hb hQ hA l hl hlen L Lb rowBits
local notation "price₁" => canonicalMatchingPrice n hn R B hR hB a ha hQ hA middle middleCount middleShape L Lb rowBits
local notation "src" => framedCoreAux (canonicalRouterCommonT + 3) 0
local notation "saved" => framedCoreAux (canonicalRouterCommonT + 3) 2
local notation "str" => framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream

def canonicalPermutationFrame : List (Fin (prime + K + 4)) := frame₀ ++ frame₁

def canonicalPermutationProgram : Pr Empty ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit :=
  .seq program₀ program₁

def canonicalPermutationPrice : ℝ := price₀ + price₁

theorem canonicalPermutation_exec
    (hn0 : 0 < n) (hnfit : n < 2 ^ L) (hBfit : B < 2 ^ Lb) (hnB : n ≤ B)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ [])
    (hrowValue : Counter.value rowBits = R)
    (rest : List (Fin (prime + K + 4)))
    (v : HS ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit)
    (S : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K))
    (ready : FramedCoreReady canonicalDirectionalStream (R * 2 ^ n) B S)
    (hstream : S.R str = l.flatten)
    (hinput : S.R src = canonicalPermutationFrame n hn R B hR hB f hQ hA l hl hlen L Lb rowBits ++ rest) :
    let E : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K) :=
      { S with R := delimitedCallAdvanced S.R src saved str (canonicalPermutationFrame n hn R B hR hB f hQ hA l hl hlen L Lb rowBits) rest (moveRecs rank l).flatten }
    ∃ (v' : HS ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ canonicalPermutationPrice n hn R B hR hB f hQ hA l hl hlen L Lb rowBits ∧
      FramedCoreReady canonicalDirectionalStream (R * 2 ^ n) B E ∧
      Exec Empty.elim (canonicalPermutationProgram n hn R B hR hB f hQ hA l hl hlen Lb rowBits)
        (mk v S) steps (mk v' E) := by
  dsimp only
  let C : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K) :=
    { S with R := delimitedCallAdvanced S.R src saved str frame₀ (frame₁ ++ rest) (middle).flatten }
  obtain ⟨v₁, m₁, hu₁, hm₁, hr₁, he₁⟩ := canonicalMatchingInput_exec n hn R B hR hB b hb hQ hA l hl hlen
    L Lb rowBits hn0 hnfit hBfit hnB hrow hrowNe hrowValue (frame₁ ++ rest) v S ready hstream
    (by simpa only [canonicalPermutationFrame, List.append_assoc] using hinput)
  have hs : C.R src = frame₁ ++ rest := by
    simp only [C, delimitedCallAdvanced, Function.update_of_ne
      (framedCoreEmbed_aux (canonicalRouterCommonT + 3) canonicalDirectionalStream 0).symm,
      Function.update_of_ne ((framedCoreAux_injective (canonicalRouterCommonT + 3)).ne (by decide : (0 : Fin 3) ≠ 2)), Function.update_self]
  have ht : C.R str = (middle).flatten := Function.update_self _ _ _
  obtain ⟨v₂, m₂, hu₂, hm₂, hr₂, he₂⟩ := canonicalMatchingInput_exec n hn R B hR hB a ha hQ hA middle middleCount middleShape
    L Lb rowBits hn0 hnfit hBfit hnB hrow hrowNe hrowValue rest v₁ C hr₁ ht hs
  have hout : moveRecs σ middle = moveRecs rank l := (moveRecs_trans π σ l hl).symm
  rw [hout] at he₂ hr₂
  dsimp only [C] at he₁ he₂ hr₂
  have hsa : src ≠ saved := (framedCoreAux_injective (canonicalRouterCommonT + 3)).ne (by decide)
  have hss : src ≠ str := (framedCoreEmbed_aux (canonicalRouterCommonT + 3) canonicalDirectionalStream 0).symm
  have has : saved ≠ str := (framedCoreEmbed_aux (canonicalRouterCommonT + 3) canonicalDirectionalStream 2).symm
  simp only [delimitedCallAdvanced_comp src saved str hsa hss has] at he₂ hr₂
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, ?_, hr₂, ?_⟩
  · push_cast
    exact add_le_add hm₁ hm₂
  · exact Exec.seq he₁ he₂

local notation "frame" => canonicalPermutationFrame n hn R B hR hB f hQ hA l hl hlen L Lb rowBits
local notation "program" => canonicalPermutationProgram n hn R B hR hB f hQ hA l hl hlen Lb rowBits
local notation "price" => canonicalPermutationPrice n hn R B hR hB f hQ hA l hl hlen L Lb rowBits
local notation "output" => List.flatten (moveRecs rank l)

theorem canonicalPermutation_restored_exec
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
  obtain ⟨v₁, m₁, hu₁, hm₁, _, he₁⟩ := canonicalPermutation_exec n hn R B hR hB f hQ hA l hl hlen
    L Lb rowBits hn0 hnfit hBfit hnB hrow hrowNe hrowValue [] v S ready hstream (by simpa using hinput)
  let C : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K) :=
    { S with R := delimitedCallAdvanced S.R src saved str frame [] output }
  have hsa : src ≠ saved := (framedCoreAux_injective (canonicalRouterCommonT + 3)).ne (by decide)
  have hss : src ≠ str := (framedCoreEmbed_aux (canonicalRouterCommonT + 3) canonicalDirectionalStream 0).symm
  have has : saved ≠ str := (framedCoreEmbed_aux (canonicalRouterCommonT + 3) canonicalDirectionalStream 2).symm
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec Empty.elim saved src hsa.symm id v₁ C
  have hf := delimitedCallAdvanced_rewind src saved str hsa hss has S.R frame output hinput hsaved
  have harchive : C.R saved = (frame).reverse := by
    simp only [C, delimitedCallAdvanced, Function.update_of_ne has, Function.update_self, hsaved, List.append_nil]
  dsimp only at hf
  dsimp only [C] at he₂ harchive
  rw [hf, harchive, List.length_reverse] at he₂
  refine ⟨v₂, m₁ + (2 * (frame).length + 2), hu₂.trans hu₁, ?_, Exec.seq he₁ he₂⟩
  push_cast
  exact add_le_add hm₁ (le_refl _)

end
end IntegerMultBounds.MathlibTM2.Routing
