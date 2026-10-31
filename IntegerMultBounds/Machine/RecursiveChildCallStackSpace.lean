module

public import IntegerMultBounds.Machine.RecursiveChildCallSetup

/-! Exact descriptor and return-code allocation at recursive call boundaries. -/
@[expose] public section
namespace IntegerMultBounds.Machine.RecursiveChildCallSetup
open BinaryDescriptorFrames
variable {q k : ℕ}

theorem savedStacks_descriptor_head (hs : Fin 6 → List Bool) (st : Tapes 2 q)
    (code : FiniteReturnStack.Code k) :
    (savedStacks hs st code).head 0 = st.head 0+span fields (words hs) := by
  simp only [savedStacks,pushed]
  rw [show Fin.natAdd 38 (0 : Fin 2) = descriptorStack by rfl]
  have hf := (FiniteReturnStackAt.pushed_frame pcStack descriptorStack (by decide) code
    (saved descriptorStack fields (words hs) (bank hs st))).1
  have hh := saved_head descriptorStack fields (words hs) (bank hs st)
  have hb : (bank hs st).head descriptorStack = st.head 0 := by
    change (bank hs st).head (Fin.natAdd 38 (0 : Fin 2)) = _
    simp only [bank,Tapes.append,Fin.addCases_right]
  exact hf.trans (hh.trans (congrArg (fun h => h+(span fields (words hs) : ℤ)) hb))

theorem savedStacks_descriptor_head_le (hs : Fin 6 → List Bool) (st : Tapes 2 q)
    (code : FiniteReturnStack.Code k) (L : ℕ) (hL : ∀ i, (hs i).length ≤ L) :
    (savedStacks hs st code).head 0 ≤ st.head 0+6*(L+1) := by
  have h := span_le fields (words hs) L (by
    intro i hi
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
    simpa only [words_header] using hL j)
  simp only [fields,List.length_ofFn] at h
  rw [savedStacks_descriptor_head]
  exact Int.add_le_add_left (by exact_mod_cast h) _

theorem savedStacks_pc_head (hs : Fin 6 → List Bool) (st : Tapes 2 q)
    (code : FiniteReturnStack.Code k) : (savedStacks hs st code).head 1 = st.head 1+k := by
  simp only [savedStacks,pushed]
  rw [show Fin.natAdd 38 (1 : Fin 2) = pcStack by rfl]
  simp only [FiniteReturnStackAt.pushed,SharedPlacementAlphabet.setTape,Function.update_self]
  rw [(saved_frame descriptorStack fields (words hs) (bank hs st) pcStack (by decide)).1]
  have hb : (bank hs st).head pcStack = st.head 1 := by
    change (bank hs st).head (Fin.natAdd 38 (1 : Fin 2)) = _
    simp only [bank,Tapes.append,Fin.addCases_right]
  exact congrArg (fun h => h+(k : ℤ)) hb

end IntegerMultBounds.Machine.RecursiveChildCallSetup
