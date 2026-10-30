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

theorem hostFrameStock_congr {T A : ℕ} {S F : Stacks T A}
    (hi : F.inp = S.inp) (ho : F.out = S.out) (hl : F.L = S.L) :
    hostFrameStock F = hostFrameStock S := by
  unfold hostFrameStock
  apply Finset.sum_congr rfl
  intro k hk
  cases k with
  | inp => simpa only [Stacks.get] using congrArg List.length hi
  | out => simpa only [Stacks.get] using congrArg List.length ho
  | lt i => simp only [Stacks.get,hl]
  | rt i =>
    have hm : HK.rt i ∈ Finset.univ.map
        (⟨HK.rt,fun _ _ h => HK.rt.inj h⟩ : Fin T ↪ HK T) :=
      Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩
    exact False.elim ((Finset.mem_compl.mp hk) hm)

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

/-- Register-wise allowances are summed once at an iteration boundary. -/
theorem mnSize_mk_le_allowance {T Q A : ℕ} {U : Type}
    (v vf : HS T Q A U) (S F : Stacks T A) (allowance : Fin T → ℕ)
    (hframe : hostFrameStock F ≤ hostFrameStock S)
    (hregister : ∀ i, (F.R i).length ≤ (S.R i).length+allowance i) :
    mnSize (mk vf F) ≤ mnSize (mk v S)+(∑ i, allowance i) := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hregister i)
  rw [Finset.sum_add_distrib] at hs
  rw [mnSize_mk_stock,mnSize_mk_stock]
  omega

/-- A growing output archive is the only additional boundary stock when all
other right stacks shrink or retain their lengths and the host frame is restored. -/
theorem mnSize_mk_le_archive {T Q A : ℕ} {U : Type}
    (v vf : HS T Q A U) (S F : Stacks T A) (archive : Fin T) (growth : ℕ)
    (hframe : hostFrameStock F ≤ hostFrameStock S)
    (harchive : (F.R archive).length ≤ (S.R archive).length+growth)
    (hother : ∀ i, i ≠ archive → (F.R i).length ≤ (S.R i).length) :
    mnSize (mk vf F) ≤ mnSize (mk v S)+growth := by
  classical
  have hs : (∑ i, (F.R i).length) ≤ ∑ i, ((S.R i).length+if i = archive then growth else 0) := by
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : i = archive
    · subst i
      simpa using harchive
    · simpa [hi] using hother i hi
  simp only [Finset.sum_add_distrib] at hs
  simp at hs
  rw [mnSize_mk_stock,mnSize_mk_stock]
  omega

end IntegerMultBounds.MathlibTM2.Host
