module

public import IntegerMultBounds.MathlibTM2.Routing.HaloMixedOrderRun

/-! Fixed shared-workspace ports for the two outer short-field moves. Only
exponent/local-length masters differ after halo enlargement. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloMixedPorts
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Routing.HaloPassContext

def incoming : Fin 16 → Fin 117 := ![54,70,71,55,47,48,49,50,51,52,53,39,40,41,42,92]
def outgoing : Fin 16 → Fin 117 := ![43,70,71,46,47,48,49,50,51,52,53,39,40,41,42,92]

@[simp] theorem incoming_source : incoming 11 = 39 := by decide +kernel
@[simp] theorem outgoing_source : outgoing 11 = 39 := by decide +kernel

theorem incoming_injective : Function.Injective incoming := by decide +kernel
theorem outgoing_injective : Function.Injective outgoing := by decide +kernel

theorem movement_fresh {A : ℕ} (S : Stacks 117 A) (hf : Fresh S) :
    ∀ j ∈ FieldOrderRun.scratch, S.R (incoming j) = [] ∧ S.R (outgoing j) = [] := by
  intro j hj
  simp only [FieldOrderRun.scratch,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact ⟨hf _ (Or.inr (by decide)),hf _ (Or.inr (by decide))⟩

end IntegerMultBounds.MathlibTM2.Routing.HaloMixedPorts
