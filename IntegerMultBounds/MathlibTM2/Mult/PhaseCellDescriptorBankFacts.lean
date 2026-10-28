module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorBank

/-! Distinct destination ports receive exactly their advertised packet words. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {T A : ℕ}

theorem descriptorBankR_member (fields : List (Fin T × List (Fin (A+4))))
    (hfields : (fields.map Prod.fst).Nodup) (R : Regs T A)
    (dst : Fin T) (xs : List (Fin (A+4))) (hm : (dst,xs) ∈ fields) :
    descriptorBankR fields R dst = xs++R dst := by
  induction fields generalizing R with
  | nil => simp at hm
  | cons f fields ih =>
    obtain ⟨k,ys⟩ := f
    have hn := List.nodup_cons.mp hfields
    rcases List.mem_cons.mp hm with he | hm
    · cases he
      rw [descriptorBankR,descriptorBankR_frame]
      · exact Function.update_self _ _ _
      · intro f hf he
        exact hn.1 (List.mem_map.mpr ⟨f,hf,he⟩)
    · have hkd : dst ≠ k := by
        intro he
        exact hn.1 (List.mem_map.mpr ⟨(dst,xs),hm,he⟩)
      rw [descriptorBankR,ih hn.2 _ hm,Function.update_of_ne hkd]

theorem descriptorBankR_ofFn {N : ℕ} (work : Fin N → Fin T)
    (hwork : Function.Injective work) (words : Fin N → List (Fin (A+4))) (R : Regs T A) :
    ∀ i, descriptorBankR (List.ofFn (fun j => (work j,words j))) R (work i) = words i++R (work i) := by
  intro i
  apply descriptorBankR_member
  · simpa only [List.map_ofFn,Function.comp_def] using (List.nodup_ofFn.mpr hwork)
  · exact List.mem_ofFn.mpr ⟨i,rfl⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
