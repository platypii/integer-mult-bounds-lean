module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalClassInput

/-! Nine concrete directional calls realize an original coordinate involution.
All reloads are charged; the concatenated outer input frame remains supplied. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Q K : ℕ} (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B) (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K)
    (inputs : (k : Fin 3) → CanonicalClassInput n hn R B hR hB mate hinv k hQ hA)
    (L Lb : ℕ) (rowBits : List Bool)

local notation "records" k:max => CanonicalClassInput.records (inputs k) 0
local notation "π" k:max => CanonicalClassInput.perm (inputs k)
local notation "frame" k:max => CanonicalClassInput.frame (inputs k) L Lb rowBits
local notation "program" k:max => CanonicalClassInput.program (inputs k) Lb rowBits
local notation "price" k:max => CanonicalClassInput.price (inputs k) L Lb rowBits
local notation "matchingPerm" => canonicalRouterMatchingPerm n hn mate hinv R B hR hB hQ hA
  (records 2) (CanonicalClassInput.count (inputs 2) 0) (CanonicalClassInput.shape (inputs 2) 0)
local notation "src" => framedCoreAux (canonicalRouterCommonT + 3) 0
local notation "saved" => framedCoreAux (canonicalRouterCommonT + 3) 2
local notation "str" => framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream

theorem canonicalMatchingRecords
    (hnext₁ : records 1 = moveRecs (π 2) (records 2))
    (hnext₀ : records 0 = moveRecs (π 1) (records 1)) :
    moveRecs (π 0) (records 0) = moveRecs matchingPerm (records 2) := by
  have hzero := (canonicalRouterClassPerm_records_independent n hn mate hinv 0 R B hR hB hQ hA
    (records 2) ((inputs 2).count 0) ((inputs 2).shape 0)
    (records 0) ((inputs 0).count 0) ((inputs 0).shape 0)).symm
  have hone := (canonicalRouterClassPerm_records_independent n hn mate hinv 1 R B hR hB hQ hA
    (records 2) ((inputs 2).count 0) ((inputs 2).shape 0)
    (records 1) ((inputs 1).count 0) ((inputs 1).shape 0)).symm
  change moveRecs (canonicalRouterClassPerm n hn mate hinv 0 R B hR hB hQ hA
    (records 0) ((inputs 0).count 0) ((inputs 0).shape 0)) (records 0) = _
  rw [hzero, hnext₀]
  change moveRecs _ (moveRecs (canonicalRouterClassPerm n hn mate hinv 1 R B hR hB hQ hA
    (records 1) ((inputs 1).count 0) ((inputs 1).shape 0)) (records 1)) = _
  rw [hone, hnext₁, ← moveRecs_trans _ _ (records 2) ((inputs 2).count 0),
    ← moveRecs_trans _ _ (records 2) ((inputs 2).count 0)]
  rfl

theorem canonicalMatching_exec
    (hn0 : 0 < n) (hnfit : n < 2 ^ L) (hBfit : B < 2 ^ Lb) (hnB : n ≤ B)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ [])
    (hrowValue : Counter.value rowBits = R)
    (hnext₁ : records 1 = moveRecs (π 2) (records 2))
    (hnext₀ : records 0 = moveRecs (π 1) (records 1))
    (rest : List (Fin (prime + K + 4)))
    (v : HS ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit)
    (S : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K))
    (ready : FramedCoreReady canonicalDirectionalStream (R * 2 ^ n) B S)
    (hstream : S.R str = (records 2).flatten)
    (hinput : S.R src = frame 2 ++ (frame 1 ++ (frame 0 ++ rest))) :
    let E : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K) :=
      { S with R := delimitedCallAdvanced S.R src saved str (frame 2 ++ (frame 1 ++ frame 0)) rest (moveRecs matchingPerm (records 2)).flatten }
    ∃ (v' : HS ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ (price 2 + price 1) + price 0 ∧
      FramedCoreReady canonicalDirectionalStream (R * 2 ^ n) B E ∧
      Exec Empty.elim (.seq (.seq (program 2) (program 1)) (program 0)) (mk v S) steps (mk v' E) := by
  dsimp only
  let C : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K) :=
    { S with R := delimitedCallAdvanced S.R src saved str (frame 2) (frame 1 ++ (frame 0 ++ rest)) (records 1).flatten }
  let D : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K) :=
    { C with R := delimitedCallAdvanced C.R src saved str (frame 1) (frame 0 ++ rest) (records 0).flatten }
  obtain ⟨v₁, m₁, hu₁, hm₁, hr₁, he₁⟩ := (inputs 2).exec L Lb rowBits
    hn0 hnfit hBfit hnB hrow hrowNe hrowValue (frame 1 ++ (frame 0 ++ rest)) v S ready hstream
    (by simpa only [List.append_assoc] using hinput)
  rw [← hnext₁] at he₁ hr₁
  have hs₁ : C.R src = frame 1 ++ (frame 0 ++ rest) := by
    simp only [C, delimitedCallAdvanced, Function.update_of_ne
      (framedCoreEmbed_aux (canonicalRouterCommonT + 3) canonicalDirectionalStream 0).symm,
      Function.update_of_ne ((framedCoreAux_injective (canonicalRouterCommonT + 3)).ne (by decide : (0 : Fin 3) ≠ 2)), Function.update_self]
  have ht₁ : C.R str = (records 1).flatten := Function.update_self _ _ _
  obtain ⟨v₂, m₂, hu₂, hm₂, hr₂, he₂⟩ := (inputs 1).exec L Lb rowBits
    hn0 hnfit hBfit hnB hrow hrowNe hrowValue (frame 0 ++ rest) v₁ C hr₁ ht₁ hs₁
  rw [← hnext₀] at he₂ hr₂
  have hs₂ : D.R src = frame 0 ++ rest := by
    simp only [D, delimitedCallAdvanced, Function.update_of_ne
      (framedCoreEmbed_aux (canonicalRouterCommonT + 3) canonicalDirectionalStream 0).symm,
      Function.update_of_ne ((framedCoreAux_injective (canonicalRouterCommonT + 3)).ne (by decide : (0 : Fin 3) ≠ 2)), Function.update_self]
  have ht₂ : D.R str = (records 0).flatten := Function.update_self _ _ _
  obtain ⟨v₃, m₃, hu₃, hm₃, hr₃, he₃⟩ := (inputs 0).exec L Lb rowBits
    hn0 hnfit hBfit hnB hrow hrowNe hrowValue rest v₂ D hr₂ ht₂ hs₂
  have hout := canonicalMatchingRecords n hn R B hR hB mate hinv hQ hA inputs hnext₁ hnext₀
  rw [hout] at he₃ hr₃
  dsimp only [D, C] at he₁ he₂ he₃ hr₃
  have hsa : src ≠ saved := (framedCoreAux_injective (canonicalRouterCommonT + 3)).ne (by decide)
  have hss : src ≠ str := (framedCoreEmbed_aux (canonicalRouterCommonT + 3) canonicalDirectionalStream 0).symm
  have has : saved ≠ str := (framedCoreEmbed_aux (canonicalRouterCommonT + 3) canonicalDirectionalStream 2).symm
  simp only [delimitedCallAdvanced_comp src saved str hsa hss has, List.append_assoc] at he₁ he₂ he₃ hr₃
  refine ⟨v₃, (m₁ + m₂) + m₃, hu₃.trans (hu₂.trans hu₁), ?_, hr₃, ?_⟩
  · push_cast
    exact add_le_add (add_le_add hm₁ hm₂) hm₃
  · exact Exec.seq (Exec.seq he₁ he₂) he₃

end
end IntegerMultBounds.MathlibTM2.Routing
