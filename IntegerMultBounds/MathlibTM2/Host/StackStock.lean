module

public import IntegerMultBounds.MathlibTM2.StackResources

/-! Separate right-register stock from the native and left-stack frame. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main

/-- Input, output and all left stacks; the right registers are priced separately. -/
def hostFrameStock {T A : ℕ} (S : Stacks T A) : ℕ :=
  ∑ k ∈ (Finset.univ.map (⟨HK.rt,fun _ _ h => HK.rt.inj h⟩ : Fin T ↪ HK T))ᶜ,
    (S.get k).length

theorem mnSize_mk_stock {T Q A : ℕ} {U : Type} (v : HS T Q A U) (S : Stacks T A) :
    mnSize (mk v S) = hostFrameStock S+∑ i, (S.R i).length := by
  have hright : ∑ k ∈ Finset.univ.map (⟨HK.rt,fun _ _ h => HK.rt.inj h⟩ : Fin T ↪ HK T),
      (S.get k).length = ∑ i, (S.R i).length := by
    rw [Finset.sum_map]
    rfl
  have hsum := Finset.sum_add_sum_compl
    (Finset.univ.map (⟨HK.rt,fun _ _ h => HK.rt.inj h⟩ : Fin T ↪ HK T))
    (fun k => (S.get k).length)
  rw [hright] at hsum
  change _+hostFrameStock S = mnSize (mk v S) at hsum
  omega

end IntegerMultBounds.MathlibTM2.Host
