module

public import IntegerMultBounds.MathlibTM2.Host.StackStock

/-! A finite bank of bounded control headers is charged once at loop boundaries. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main

/-- Only the listed headers may grow. They need not have the same lengths, and
repeated tape names merely overestimate the allowance. -/
theorem mnSize_mk_le_header_bank {T Q A N : ℕ} {U : Type}
    (v vf : HS T Q A U) (S F : Stacks T A) (header : Fin N → Fin T) (V : ℕ)
    (hi : F.inp = S.inp) (ho : F.out = S.out) (hl : F.L = S.L)
    (hheader : ∀ j, (F.R (header j)).length ≤ V)
    (hother : ∀ i, (∀ j, i ≠ header j) → (F.R i).length ≤ (S.R i).length) :
    mnSize (mk vf F) ≤ mnSize (mk v S)+N*V := by
  let allowance := fun i => ∑ j : Fin N, if i = header j then V else 0
  have hh := mnSize_mk_le_allowance v vf S F allowance
    (le_of_eq (hostFrameStock_congr hi ho hl)) (by
      intro i
      by_cases he : ∃ j, i = header j
      · obtain ⟨j,rfl⟩ := he
        have hsum : V ≤ allowance (header j) := by
          have h := Finset.single_le_sum (s := Finset.univ)
            (f := fun k : Fin N => if header j = header k then V else 0)
            (fun k _ => Nat.zero_le _) (Finset.mem_univ j)
          simpa [allowance] using h
        exact (hheader j).trans (by omega)
      · exact (hother i (by simpa only [not_exists] using he)).trans (Nat.le_add_right _ _))
  have hsum : (∑ i, allowance i) = N*V := by
    simp only [allowance]
    rw [Finset.sum_comm]
    simp
  simpa only [hsum] using hh

end IntegerMultBounds.MathlibTM2.Host
