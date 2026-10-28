module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyDispatch

/-! The numerical result relation bounds accumulated output by the physical input tape. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T A s : ℕ} [NeZero s]

theorem familyDispatchProduced_length {p l t : ℕ}
    {x y : FamilyDispatchInput s A → (ZMod s → GaussianInt) → ZMod s → ℝ}
    {r : FamilyDispatchInput s A} {output : List (Fin (A+4))}
    (h : FamilyDispatchProduced p l t x y r output) :
    output.length = r.inputs.length*s*r.width p l t := by
  obtain ⟨Zs,rfl,happrox⟩ := h
  have hlen := List.Forall₂.length_eq happrox
  dsimp only [FamilyDispatchInput.output]
  rw [familyBatchWords_length,← hlen]

theorem familyDispatchProduced_length_le_tape {p l t : ℕ} {d : ℝ}
    {x y : FamilyDispatchInput s A → (ZMod s → GaussianInt) → ZMod s → ℝ}
    (work : Fin 303 → Fin T) {r : FamilyDispatchInput s A} {output : List (Fin (A+4))}
    (hr : FamilyDispatchReady p l t d r) (h : FamilyDispatchProduced p l t x y r output) :
    output.length ≤ (descriptorBankTape (placedDescriptorFields work r.words)).length := by
  have hs : (r.words 110).length ≤ ∑ i, (r.words i).length :=
    Finset.single_le_sum (f := fun i : Fin 303 => (r.words i).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (110 : Fin 303))
  rw [hr.source,familyBatchWords_length] at hs
  rw [familyDispatchProduced_length h,descriptorBankTape_length]
  simp only [placedDescriptorFields,List.map_ofFn,Function.comp_def,List.sum_ofFn,List.length_ofFn]
  omega

theorem familyDispatch_outputs_length_le_tape {p l t : ℕ} {d : ℝ}
    {x y : FamilyDispatchInput s A → (ZMod s → GaussianInt) → ZMod s → ℝ}
    (work : Fin 303 → Fin T) {records : List (FamilyDispatchInput s A)}
    {outputs : List (List (Fin (A+4)))}
    (hready : ∀ r ∈ records, FamilyDispatchReady p l t d r)
    (h : List.Forall₂ (FamilyDispatchProduced p l t x y) records outputs) :
    outputs.reverse.flatten.length ≤ (descriptorScheduleTape work FamilyDispatchInput.words records).length := by
  have hg : outputs.flatten.length ≤ (descriptorScheduleTape work FamilyDispatchInput.words records).length := by
    induction h with
    | nil => simp [descriptorScheduleTape]
    | @cons r output records outputs hhead htail ih =>
      have hc := familyDispatchProduced_length_le_tape work (hready r (by simp)) hhead
      have ht := ih (fun r hr => hready r (by simp [hr]))
      simp only [List.flatten_cons,List.length_append,descriptorScheduleTape,List.flatMap_cons,List.length_append] at ht ⊢
      omega
  simpa only [List.length_flatten,List.map_reverse,List.sum_reverse] using hg

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
