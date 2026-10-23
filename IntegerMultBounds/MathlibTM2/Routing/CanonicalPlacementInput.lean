module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalOuterInput
public import IntegerMultBounds.MathlibTM2.Routing.SharedScheduleInput

/-! The placement extension preserves the complete constructed repair stack.
Its legacy swap bank starts empty; only binary schedule operands are installed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
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

end
end IntegerMultBounds.MathlibTM2.Routing
