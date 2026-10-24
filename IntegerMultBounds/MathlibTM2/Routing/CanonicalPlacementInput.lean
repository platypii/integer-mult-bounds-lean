module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalOuterInput
public import IntegerMultBounds.MathlibTM2.Routing.SharedScheduleInput
public import IntegerMultBounds.MathlibTM2.Routing.BinaryScheduleCalls

/-! The placement extension preserves the complete constructed repair stack.
Its legacy swap bank starts empty; only binary schedule operands are installed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {N t₀ n A : ℕ}

def canonicalPlacementInputStack (src : Fin N) (S : Stacks N A) (spec : Fin 3 → BlockExchangeSpec n)
    (Lc L B : ℕ) (rowBits : List Bool) (stream : List (Fin (A + 4))) : Stacks (sharedScheduleT N t₀) A :=
  ⟨S.inp, S.out, Function.extend sharedCoreEmbed S.L (fun _ => []),
    sharedScheduleInputBank src S.R spec (fun _ => []) Lc L B rowBits stream⟩

theorem canonicalPlacementInputStack_project (src : Fin N) (S : Stacks N A) (spec : Fin 3 → BlockExchangeSpec n)
    (Lc L B : ℕ) (rowBits : List Bool) (stream : List (Fin (A + 4))) :
    embStk sharedCoreEmbed (canonicalPlacementInputStack (t₀ := t₀) src S spec Lc L B rowBits stream) = S := by
  have hL : (embStk sharedCoreEmbed (canonicalPlacementInputStack (t₀ := t₀) src S spec Lc L B rowBits stream)).L = S.L := by
    funext j
    change Function.extend (sharedCoreEmbed (N := N) (t₀ := t₀)) S.L (fun _ => []) (sharedCoreEmbed j) = S.L j
    exact (sharedCoreEmbed_injective (N := N) (t₀ := t₀)).extend_apply _ _ j
  have hR : (embStk sharedCoreEmbed (canonicalPlacementInputStack (t₀ := t₀) src S spec Lc L B rowBits stream)).R = S.R := by
    funext j
    exact sharedScheduleInputBank_core src S.R spec (fun _ => []) Lc L B rowBits stream j
  exact congrArg₂ (fun L R => (⟨S.inp, S.out, L, R⟩ : Stacks N A)) hL hR

theorem canonicalPlacementInputStack_left (src : Fin N) (S : Stacks N A) (spec : Fin 3 → BlockExchangeSpec n)
    (Lc L B : ℕ) (rowBits : List Bool) (stream : List (Fin (A + 4))) (hL : ∀ j, S.L j = []) :
    ∀ j, (canonicalPlacementInputStack (t₀ := t₀) src S spec Lc L B rowBits stream).L j = [] := by
  intro j
  change Function.extend sharedCoreEmbed S.L (fun _ => []) j = []
  by_cases hcore : ∃ i, sharedCoreEmbed (N := N) (t₀ := t₀) i = j
  · obtain ⟨i, rfl⟩ := hcore
    rw [sharedCoreEmbed_injective.extend_apply]
    exact hL i
  · exact Function.extend_apply' _ _ _ hcore

theorem canonicalPlacementInputStack_swapBank (src : Fin N) (S : Stacks N A)
    (spec : Fin 3 → BlockExchangeSpec n) (Lc L B : ℕ)
    (rowBits : List Bool) (stream : List (Fin (A + 4))) (hstream : S.R src = stream)
    (j : Fin (swapT t₀)) :
    (canonicalPlacementInputStack (t₀ := t₀) src S spec Lc L B rowBits stream).R
      (sharedScheduleSlot src (.bank j)) = [] := by
  have h := sharedScheduleInputBank_schedule src S.R spec (fun _ => []) Lc L B rowBits stream
    hstream (.bank j)
  simpa only [canonicalPlacementInputStack, binaryScheduleInputWords] using h

theorem canonicalPlacementInputStack_swapBank_length (src : Fin N) (S : Stacks N A)
    (spec : Fin 3 → BlockExchangeSpec n) (Lc L B : ℕ)
    (rowBits : List Bool) (stream : List (Fin (A + 4))) (hstream : S.R src = stream) :
    (∑ j : Fin (swapT t₀),
      ((canonicalPlacementInputStack (t₀ := t₀) src S spec Lc L B rowBits stream).R
        (sharedScheduleSlot src (.bank j))).length) = 0 := by
  simp only [canonicalPlacementInputStack_swapBank src S spec Lc L B rowBits stream hstream,
    List.length_nil, Finset.sum_const_zero]

theorem canonicalPlacementInputStack_scheduleCost_le {Q K R : ℕ}
    (src : Fin N) (S : Stacks N (prime + K)) (spec : Fin 3 → BlockExchangeSpec n)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd) (hpay : ∀ k, hd k ≠ pay)
    (hQ : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ sharedScheduleT N t₀)
    (hR : 0 < R) (B : ℕ) (hB : 0 < B) (rowBits : List Bool) (Lc L : ℕ)
    (hn : n < 2 ^ Lc) (hBin : B < 2 ^ L)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ [])
    (hrowValue : Counter.value rowBits = R)
    (stream : List (Fin (prime + K + 4))) (hstream : S.R src = stream) (js : List (Fin 3)) :
    binaryExchangeChainCost
      (binaryScheduleCalls (sharedScheduleSlot src) (sharedScheduleSlot_injective src)
        hd pay hhd hpay hQ hT spec hR hB rowBits Lc L hn hBin hrow hrowNe hrowValue)
      (canonicalPlacementInputStack src S spec Lc L B rowBits stream) js ≤
      (3 * swapConst * (sharedScheduleT N t₀ + 12 * swapT t₀ + 5 : ℕ) * (R * 2 ^ n * B : ℕ)) *
        (js.map (fun j => ((max 1 (spec j).w : ℕ) : ℝ) ^ Parameters.tau)).sum +
      js.length * (generatedExchangeUniformOverhead t₀ (sharedScheduleT N t₀) n R B L rowBits.length Lc 0 +
        (3 * (Lc * (4 * n + 31) + 2 * n + 26) + 10 * Lc + 12) + (2 * n + 2 * Lc + 9) : ℕ) + 1 := by
  exact binaryScheduleChainCost_le (sharedScheduleSlot src) (sharedScheduleSlot_injective src)
    hd pay hhd hpay hQ hT spec hR hB rowBits Lc L hn hBin hrow hrowNe hrowValue
    (canonicalPlacementInputStack src S spec Lc L B rowBits stream)
    (canonicalPlacementInputStack_swapBank src S spec Lc L B rowBits stream hstream) js

/-- Placement adds scalar coordinates and the row counter, with blank swap workspace. -/
theorem canonicalPlacementInputStack_length_le (src : Fin N) (S : Stacks N A)
    (spec : Fin 3 → BlockExchangeSpec n) (Lc L B C : ℕ)
    (rowBits : List Bool) (stream : List (Fin (A + 4)))
    (hcore : ∀ j, j ≠ src → (S.R j).length ≤ C)
    (j : Fin (sharedScheduleT N t₀)) (hj : j ≠ sharedCoreEmbed src) :
    ((canonicalPlacementInputStack (t₀ := t₀) src S spec Lc L B rowBits stream).R j).length ≤
      C + Lc + L + rowBits.length := by
  by_cases hc : ∃ i, sharedCoreEmbed (N := N) (t₀ := t₀) i = j
  · obtain ⟨i, rfl⟩ := hc
    simp only [canonicalPlacementInputStack, sharedScheduleInputBank_core]
    have hi := hcore i (fun he => hj (congrArg sharedCoreEmbed he))
    omega
  · change (Function.extend sharedCoreEmbed S.R _ j).length ≤ _
    rw [Function.extend_apply' _ _ _ hc]
    by_cases hs : ∃ r, sharedScheduleSlot (t₀ := t₀) src r = j
    · obtain ⟨r, rfl⟩ := hs
      rw [binaryScheduleInputBank_at _ (sharedScheduleSlot_injective src)]
      have hr : r ≠ .str := by intro he; subst r; exact hj (sharedScheduleSlot_str src)
      cases r <;> simp only [binaryScheduleInputWords, length_binSyms, List.length_map, List.length_nil]
      all_goals first | omega | exact (hr rfl).elim
    · unfold binaryScheduleInputBank
      rw [Function.extend_apply' _ _ _ hs]
      exact Nat.zero_le _


/-- Placement adds only binary operands, so a framing delimiter above seven
cannot occur in a canonical input bank. -/
theorem canonicalPlacementInputStack_small (src : Fin N) (S : Stacks N A)
    (spec : Fin 3 → BlockExchangeSpec n) (Lc L B : ℕ)
    (rowBits : List Bool) (stream : List (Fin (A + 4)))
    (hcore : ∀ j, ∀ x ∈ S.R j, x.val < 8)
    (hstream : ∀ x ∈ stream, x.val < 8) :
    ∀ j, ∀ x ∈ (canonicalPlacementInputStack (t₀ := t₀) src S spec Lc L B rowBits stream).R j,
      x.val < 8 := by
  intro j
  by_cases hc : ∃ i, sharedCoreEmbed (N := N) (t₀ := t₀) i = j
  · obtain ⟨i, rfl⟩ := hc
    simpa only [canonicalPlacementInputStack, sharedScheduleInputBank_core] using hcore i
  · change ∀ x ∈ Function.extend sharedCoreEmbed S.R _ j, x.val < 8
    rw [Function.extend_apply' _ _ _ hc]
    by_cases hs : ∃ r, sharedScheduleSlot (t₀ := t₀) src r = j
    · obtain ⟨r, rfl⟩ := hs
      rw [binaryScheduleInputBank_at _ (sharedScheduleSlot_injective src)]
      cases r <;> simp only [binaryScheduleInputWords]
      all_goals first
        | exact canonicalScalarWord_small _ _
        | exact hstream
        | (intro x hx; obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
           simp only [bitSymbol]; split <;> omega)
        | simp
    · unfold binaryScheduleInputBank
      rw [Function.extend_apply' _ _ _ hs]
      simp

end
end IntegerMultBounds.MathlibTM2.Routing
