module

public import IntegerMultBounds.Machine.RecursiveViewFrame

/-! Exact storage of saved recursive view headers. The two frames retained
while a child runs cost twelve header words, independently of child runtime. -/
@[expose] public section
namespace IntegerMultBounds.Machine.RecursiveViewFrame
open BinaryDescriptorFrames
variable {q : ℕ}

theorem savedStack_head (hs : Fin 6 → List Bool) (st : Tapes 1 q) :
    (savedStack hs st).head 0 = st.head 0+span fields (words hs) := by
  change (saved stack fields (words hs) (bank hs st)).head stack = _
  rw [saved_head]
  rfl

theorem savedStack_head_le (hs : Fin 6 → List Bool) (st : Tapes 1 q) (L : ℕ)
    (hL : ∀ i, (hs i).length ≤ L) :
    (savedStack hs st).head 0 ≤ st.head 0+6*(L+1) := by
  have h := span_le fields (words hs) L (by
    intro i hi
    obtain ⟨j,rfl⟩ := (mem_fields i).mp hi
    simpa only [words_slot] using hL j)
  rw [fields_length] at h
  rw [savedStack_head]
  exact Int.add_le_add_left (by exact_mod_cast h) _

theorem savedStack_pair_head_le (hs gs : Fin 6 → List Bool) (st : Tapes 1 q) (L : ℕ)
    (hh : ∀ i, (hs i).length ≤ L) (hg : ∀ i, (gs i).length ≤ L) :
    (savedStack gs (savedStack hs st)).head 0 ≤ st.head 0+12*(L+1) := by
  have h := savedStack_head_le hs st L hh
  have h' := savedStack_head_le gs (savedStack hs st) L hg
  omega

theorem savedStack_outside (hs : Fin 6 → List Bool) (st : Tapes 1 q) (z : ℤ)
    (hz : z < st.head 0 ∨ (savedStack hs st).head 0 ≤ z) :
    (savedStack hs st).tape 0 z = st.tape 0 z := by
  rw [savedStack_head] at hz
  exact saved_outside stack fields (words hs) (bank hs st) z hz

end IntegerMultBounds.Machine.RecursiveViewFrame
